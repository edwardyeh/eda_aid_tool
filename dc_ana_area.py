#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# SPDX-License-Identifier: GPL-2.0-only
#
# Design Compiler Area Report Analysis
#
# Copyright (C) 2022 Yeh, Hsin-Hsien <yhh76227@gmail.com>
#
import argparse
import copy
import gzip
import math
import os
import re
import sys
import textwrap
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Any

from simpletools.text import Align, Array, Border, Cell, SimpleTable
from .utils.common import PKG_VERSION, DC_AREA_VER

VERSION = f"dc_ana_area version {DC_AREA_VER} ({PKG_VERSION})"


### Global Parameter ###


DEFAULT_PATH_COL_SIZE = 32
DEFAULT_AREA_COL_SIZE = 8
ISYM = f"{0x251c:c}{0x2500:c}"      # fork symbol
ESYM = f"{0x2514:c}{0x2500:c}"      # end symbol
BSYM = f"{0x2502:c} "               # through symbol

hide_op = {
    '>' : lambda a, b: a > b,
    '<' : lambda a, b: a < b,
    '==': lambda a, b: a == b,
    '>=': lambda a, b: a >= b,
    '<=': lambda a, b: a <= b
}

# at: area total
# pt: percent total
hide_cmp = {
    'at': lambda node, op, val: hide_op[op](node.total_area, val),
    'pt': lambda node, op, val: hide_op[op](node.total_percent, val)
}


### Class Defintion ###


class UnitType(IntEnum):
    NONE = 0
    NORM = 1
    SCI  = 2


@dataclass(slots=True)
class UnitAttr:
    type:  UnitType = UnitType.NONE
    value: float = 1
    tag:   str   = ''
    info:  str   = '1'


@dataclass(slots=True)
class TableAttr:
    area_fs:       str
    ratio:         float
    unit:          UnitAttr
    dec_place:     int
    is_show_ts:    bool
    is_brief:      bool
    is_logic_sep:  bool
    is_reorder:    bool
    is_show_level: bool
    is_nosplit:    bool
    view_type:     str
    trace_root:    str
    proc_mode:     str
    vtop_name:     str  = 'VIRTUAL_TOP'
    is_verbose:    bool = False
    is_sub_sum:    bool = field(init=False, default=False)
    path_col_size: int  = DEFAULT_PATH_COL_SIZE
    design_name:   list = field(default_factory=list)


@dataclass(slots=True)
class SumGroup:
    name:       str
    total_area: int = 0
    comb_area:  int = 0
    seq_area:   int = 0
    bbox_area:  int = 0
    diff_area:  int = 0


class Node:
    def __init__(self, dname: str, bname: str, level: int,
                 total_area: float=0.0, comb_area: float=0.0,
                 seq_area: float=0.0, bbox_area: float=0.0,
                 parent=None, childs=None, scans=None):
        self.dname      = dname
        self.bname      = bname
        self.level      = level
        self.total_area = total_area
        self.comb_area  = comb_area
        self.seq_area   = seq_area
        self.bbox_area  = bbox_area
        self.parent     = parent
        self.childs     = set() if childs is None else childs
        self.scans      = set() if scans is None else sncas

        self.total_percent = -1
        self.is_show       = False
        self.is_hide       = False
        self.is_sub_sum    = False
        self.sub_comb_area = None
        self.sub_seq_area  = None
        self.sub_bbox_area = None
        self.gid_dict      = dict()
        self.is_sub_root   = False
        self.sr_name       = None
        self.tag_name      = None
        self.inst_name     = None


@dataclass(slots=True)
class Design:
    top_node:   Any   = None
    total_area: float = 0
    comb_area:  float = 0
    seq_area:   float = 0
    bbox_area:  float = 0
    max_lv:     int   = 0
    node_dict:  dict  = field(default_factory=dict)
    diff_dict:  dict  = field(default_factory=dict)
    root_list:  list  = field(default_factory=list)
    level_list: list  = field(default_factory=list)


class DesignDB:
    ghead = [('name', 'Summation Group.'), ('total', 'Absolute.Total'),
             ('comb', 'Combi-.national'), ('seq', 'Noncombi-.national'),
             ('bbox', 'Black-.Boxes'), ('logic', 'Logic.Area'),
             ('ptotal', 'Percent.Total'), ('pbox', 'Percent.Boxes'),
             ('sub_sum', 'Submodule.Summation')]
    ahead = ([('item', 'Item')] + ghead[1:] +
             [('hide', 'Is Hide?'), ('did', 'Design ID'), ('rid', 'Root ID'),
              ('level', 'Level'), ('attr', 'Attr'),
              ('name', 'Instance')])
    def __init__(self):
        self.virtual_top = Design(top_node='virtual_top')
        self.design_list = []
        self.group_table = SimpleTable(self.ghead, is_partp=False)
        self.area_table = None


### Sub Function ###


def load_area(area_fps, table_attr: TableAttr) -> list:
    """Load area report"""
    design_list = []
    area_ratio = table_attr.ratio
    area_unit = table_attr.unit.value

    if type(area_fps) is not list:
        area_fps = [area_fps]

    for fid, area_fp in enumerate(area_fps, start=0):
        table_attr.design_name.append(f'Design{fid}')
        design_list.append(design:=Design())
        node_dict = design.node_dict
        top_node = None
        fsm = ds_max_lv = 0
        ds_comb_area = ds_seq_area = ds_bbox_area = 0

        with open(area_fp) as f:
            line = f.readline()
            while line:
                if fsm == 0:
                    if line.strip().startswith("Hierarchical cell"):
                        fsm = 1
                if fsm == 1:
                    if line.strip().startswith("---"):
                        fsm = 2
                elif fsm == 2 and len(toks:=line.split()):
                    # report ending check
                    if toks[0].startswith("---"):
                        design.total_area = top_node.total_area
                        design.comb_area = ds_comb_area
                        design.seq_area = ds_seq_area
                        design.bbox_area = ds_bbox_area
                        design.max_lv = ds_max_lv
                        design.top_node = top_node
                        break

                    path = toks[0]
                    names = path.split('/')
                    dname = '/'.join(names[:-1])  # dirname
                    bname = names[-1]             # basename
                    del toks[0]

                    if len(toks) == 0:  # total area
                        line = f.readline()
                        toks = line.split()
                    total_area = float(toks[0]) * area_ratio / area_unit
                    del toks[0]

                    if len(toks) == 0:  # total percent
                        line = f.readline()
                        toks = line.split()
                    del toks[0]

                    if len(toks) == 0:  # combination area
                        line = f.readline()
                        toks = line.split()
                    comb_area = float(toks[0]) * area_ratio / area_unit
                    del toks[0]

                    if len(toks) == 0:  # sequence area
                        line = f.readline()
                        toks = line.split()
                    seq_area = float(toks[0]) * area_ratio / area_unit
                    del toks[0]

                    if len(toks) == 0:  # bbox area
                        line = f.readline()
                        toks = line.split()
                    bbox_area = float(toks[0]) * area_ratio / area_unit
                    del toks[0]

                    ds_comb_area += comb_area
                    ds_seq_area += seq_area
                    ds_bbox_area += bbox_area

                    if top_node is None:
                        top_node = node = Node(dname, bname, 0, total_area,
                                               comb_area, seq_area, bbox_area)
                        top_node.total_percent = 1.0
                    elif len(names) == 1:
                        node = Node(dname, bname, 1, total_area, comb_area,
                                    seq_area, bbox_area, parent=top_node)
                        node.total_percent = total_area / top_node.total_area
                        top_node.childs.add(node)
                    else:
                        parent_node = node_dict[dname]
                        node = Node(dname, bname, len(names), total_area,
                                    comb_area, seq_area, bbox_area,
                                    parent=parent_node)
                        node.total_percent = total_area / top_node.total_area
                        parent_node.childs.add(node)

                    node_dict[path] = node

                    if node.level > ds_max_lv:
                        ds_max_lv = node.level
                    if table_attr.proc_mode == 'norm':
                        node.scans = node.childs
                    if table_attr.proc_mode == 'norm' or table_attr.is_verbose:
                        node.is_show = True

                line = f.readline()
    return design_list


def load_cfg(cfg_fp, design_db: DesignDB, table_attr: TableAttr):
    """Load configuration"""
    dslist = design_db.design_list
    gtable = design_db.group_table

    regexp_dplen  = re.compile(r'^default_path_length:\s{0,80}(?P<size>\d{1,3})')
    regexp_dsname = re.compile(r'^design_name:\s{0,80}(?P<pat>[^#]+)')
    regexp_grp    = re.compile(r'^grp(?P<id>\d{1,2})?:\s{0,80}(?P<pat>[^#]+)')
    regexp_tag    = re.compile(r'^tag(?P<id>\d)?:\s{0,80}(?P<pat>[^#]+)')
    regexp_inst   = re.compile(r'^inst(?P<id>\d)?:\s{0,80}(?P<pat>[^#]+)')
    regexp_re     = re.compile(r'^re(?P<id>\d)?:\s{0,80}(?P<pat>[^#]+)')
    regexp_node   = re.compile(r'^(?:(?P<id>\d):)?(?P<pat>[^#]+)')

    with open(cfg_fp) as f:
        line_no = 0
        for line in f.readlines():
            line_no += 1
            if len(line:=line.strip()):
                if line[0] == '#':
                    continue
                try:
                    if (m:=regexp_dplen.match(line)):
                        # set path column size
                        path_len = int(m.group('size'))
                        if path_len > 10:
                            table_attr.path_col_size = path_len
                        else:
                            table_attr.path_col_size = 10
                        continue
                    if (m:=regexp_dsname.match(line)):
                        # set design names
                        for pattern in m.group('pat').split():
                            did, name = pattern.split('-')
                            try:
                                table_attr.design_name[int(did)] = name
                            except IndexError:
                                pass
                        continue
                    if (m:=regexp_grp.match(line)):
                        # set group summation
                        if not m.group('id'):
                            raise SyntaxError("Set group name should specify" +
                                              " a group ID.")
                        name = m.group('pat').strip('\"\'\n ')
                        gkey = m.group('id')
                        if gkey not in gtable.index.id:
                            gtable.add_row(gkey, '', [name], init=0.0)
                        continue
                    if (m:=regexp_tag.match(line)):
                        # replace instance path for path/inst view
                        path, tag = m.group('pat').split()
                        if (did:=m.group('id')):
                            dslist[int(did)].node_dict[path].tag_name = tag
                        else:
                            for design in dslist:
                                try:
                                    design.node_dict[path].tag_name = tag
                                except:
                                    pass
                        continue
                    if (m:=regexp_inst.match(line)):
                        # replace instance name
                        path, inst = m.group('pat').split()
                        if (did:=m.group('id')):
                            dslist[int(did)].node_dict[path].inst_name = inst
                        else:
                            for design in dslist:
                                try:
                                    design.node_dict[path].inst_name = inst
                                except:
                                    pass
                        continue

                    ## Load node from configuration ##

                    if (m:=regexp_re.match(line)):
                        # instance select by regular expression
                        pattern, *cmd_list = m.group('pat').split()
                        regexp = re.compile(pattern)
                        if (did:=m.group('id')):
                            start_id = int(did)
                            end_id = start_id + 1
                        else:
                            start_id = 0
                            end_id = len(dslist)

                        for did in range(start_id, end_id):
                            node_dict = dslist[did].node_dict
                            level_list = dslist[did].level_list
                            for path in node_dict.keys():
                                if regexp.match(path):
                                    node = node_dict[path]
                                    node.is_show = True
                                    max_lv = len(level_list) - 1
                                    if max_lv < node.level:
                                        for i in range(node.level-max_lv):
                                            level_list.append(set())
                                    level_list[node.level].add(node)
                                    parse_cmd(node, cmd_list, dslist[did],
                                              gtable, table_attr)
                        continue
                    if (m:=regexp_node.match(line)):
                        # instance choose
                        path, *cmd_list = m.group('pat').split()
                        if (did:=m.group('id')):
                            start_id = int(did)
                            end_id = start_id + 1
                        else:
                            start_id = 0
                            end_id = len(dslist)

                        for did in range(start_id, end_id):
                            node_dict = dslist[did].node_dict
                            level_list = dslist[did].level_list
                            if (node:=node_dict.get(path)):
                                node.is_show = True
                                max_lv = len(level_list) - 1
                                if max_lv < node.level:
                                    for i in range(node.level-max_lv):
                                        level_list.append(set())
                                level_list[node.level].add(node)
                                parse_cmd(node, cmd_list, dslist[did],
                                          gtable, table_attr)
                        continue
                except Exception as e:
                    print(f"\nLOAD_CONFIG: syntax error (line:{line_no}).\n")
                    raise e

    if gtable.max_row > 0:
        table_attr.is_sub_sum = True

    ## backward scan link ##

    for design in dslist:
        level_list = design.level_list
        for level in range(len(level_list)-1, 0, -1):
            for node in level_list[level]:
                if node.parent is not None:
                    node.parent.scans.add(node)
                    level_list[level-1].add(node.parent)


def parse_cmd(node: Node, cmd_list: list, design: Design,
              gtable: SimpleTable, table_attr: TableAttr):
    """Parsing command"""
    end_cond = len(cmd_list)
    idx = 0

    while idx < end_cond:
        cmd = cmd_list[idx]
        idx += 1

        if cmd == '':
            continue
        if cmd == 'sum':
            sub_area_sum(node)
            table_attr.is_sub_sum = node.is_sub_sum = True
        elif cmd.startswith('hide'):
            toks = cmd.split(':')
            try:
                if len(toks) == 1:
                    node.is_hide = True
                else:
                    pat = toks[1]
                    if pat.startswith('\"'):
                        while not pat.endswith('\"'):
                            pat += f" {cmd_list[idx]}"
                            idx += 1
                    elif pat.startswith('\''):
                        while not pat.endswith('\''):
                            pat += f" {cmd_list[idx]}"
                            idx += 1
                    pat = pat.strip('\"\'\n ')
                    try:
                        re_pat = r"(\w{2})\s{0,10}([><=]{1,2})\s{0,10}(\w+)"
                        ma = re.fullmatch(re_pat, pat)
                        if ma is None or len(ma_grp:=ma.groups()) != 3:
                            raise SyntaxError
                        else:
                            node.is_hide = hide_cmp[ma_grp[0]](
                                            node, ma_grp[1], float(ma_grp[2]))
                    except Exception as e:
                        print("\nPARSE_CMD: error command syntax (cmd: hide)\n")
                        raise e
            except Exception as e:
                raise e
        elif cmd.startswith('sr'):
            node.is_sub_root = True
            design.root_list.append(node)
            toks = cmd.split(':')
            if len(toks) > 1:
                node.sr_name = toks[1].strip()
        elif cmd.startswith('add') or cmd.startswith('sub') :
            toks = cmd.split(':')
            if len(toks[0]) == 3:
                raise SyntaxError("Add or Sub instance to a group should " +
                                  "specify a group ID.")

            gid = int(toks[0][3:])
            if toks[0][0:3] == 'add':
                node.gid_dict[gid] = 1
            else:
                node.gid_dict[gid] = -1

            gkey = str(gid)
            if gkey not in gtable.index.id:
                gtable.add_row(gkey, '', [f'Group {gid}'], init=0.0)
            if len(toks) > 1:
                name = toks[1]
                if name.startswith('\"'):
                    while not name.endswith('\"'):
                        name += f" {cmd_list[idx]}"
                        idx += 1
                elif name.startswith('\''):
                    while not name.endswith('\''):
                        name += f" {cmd_list[idx]}"
                        idx += 1
                gtable[gid][0] = name.strip('\"\'\n ')
        elif cmd == 'inf':
            trace_sub_node(node, 'inf', cmd_list[idx:], design, gtable,
                           table_attr)
        elif cmd[0] == 'l':
            trace_sub_node(node, cmd[1:], cmd_list[idx:], design, gtable,
                           table_attr)
        else:
            print("\nPARSE_CMD: error command\n")
            raise SyntaxError


def trace_sub_node(cur_node: Node, trace_lv: str, cmd_list: list,
                   design: Design, gtable: SimpleTable,
                   table_attr: TableAttr):
    """Trace sub nodes"""
    level_list = design.level_list
    scan_lv = math.inf if trace_lv == 'inf' else cur_node.level + int(trace_lv)
    max_lv = len(level_list) - 1
    scan_stack = []

    if cur_node.level < scan_lv:
        cur_node.scans = cur_node.childs
        scan_stack.extend(cur_node.childs)

    while len(scan_stack):
        node = scan_stack.pop()
        node.is_show = True
        parse_cmd(node, cmd_list, design, gtable, table_attr)
        if max_lv < node.level:
            level_list.extend([set() for i in range(node.level - max_lv)])
            max_lv = node.level
        level_list[node.level].add(node)
        if node.level < scan_lv:
            node.scans = node.childs
            scan_stack.extend(node.childs)


def sub_area_sum(cur_node: Node):
    """Trace and Sum sub-node area."""
    sub_comb_area = sub_seq_area = sub_bbox_area = 0
    scan_stack = [cur_node]

    while len(scan_stack):
        node = scan_stack.pop()
        sub_comb_area += node.comb_area
        sub_seq_area  += node.seq_area
        sub_bbox_area += node.bbox_area
        scan_stack.extend(node.childs)

    cur_node.sub_comb_area = sub_comb_area
    cur_node.sub_seq_area = sub_seq_area
    cur_node.sub_bbox_area = sub_bbox_area


def show_hier_area(design_db: DesignDB, table_attr: TableAttr):
    """Show hierarchical area."""

    ## create group table and remove hide node ##

    virtual_top = design_db.virtual_top
    vtotal = virtual_top.total_area
    dslist = design_db.design_list
    gtable = design_db.group_table
    is_sub_sum = table_attr.is_sub_sum
    area_fs = table_attr.area_fs
    perc_fs = "{:6.1%}"
    path_lv = 0

    for design in dslist:
        for level in range((last_lv := len(design.level_list)-1), -1, -1):
            for node in design.level_list[level]:
                if node.gid_dict:
                    if node.sub_bbox_area is None:
                        sub_area_sum(node)
                    for gid, sign in node.gid_dict.items():
                        gtable[f'{gid}','total':'bbox'] += Array(
                            [sign * node.total_area,
                             sign * node.sub_comb_area,
                             sign * node.sub_seq_area,
                             sign * node.sub_bbox_area])
                if node.is_hide or not node.is_show:
                    if len(node.scans) == 0 and node.parent is not None:
                        node.parent.scans.remove(node)
                    else:
                        node.is_show = False
        if last_lv > path_lv:
            path_lv = last_lv

    if table_attr.proc_mode == 'norm':
        path_lv = virtual_top.max_lv

    lv_digi = len(str(path_lv))

    ## create area table ##

    design_db.area_table = (atable:=SimpleTable(design_db.ahead))

    is_multi = len(dslist) > 1
    is_virtual_en = is_multi and table_attr.trace_root != 'sub'

    if table_attr.is_show_level:
        path_name = '({}) {}'.format('T'.rjust(lv_digi), virtual_top.top_node)
    else:
        path_name = f'{virtual_top.top_node}'

    if is_virtual_en:
        atable.add_row(None, '', [
            'virtual_top',          # item
            virtual_top.total_area, # total
            virtual_top.comb_area,  # comb
            virtual_top.seq_area,   # seq
            virtual_top.bbox_area,  # bbox
            0.0,                    # logic
            0.0,                    # ptotal
            0.0,                    # pbox
            True,                   # sub_sum
            False,                  # hide
            None,                   # did
            None,                   # rid
            None,                   # level
            '',                     # attr
            path_name               # name
        ])

        last_did = -1
        for did, design in enumerate(dslist):
            if design.top_node.is_show or len(design.top_node.scans) > 0:
                last_did = did

    for did, design in enumerate(dslist):
        if table_attr.trace_root == 'sub':
            root_list = design.root_list
        else:
            root_list = [design.top_node]

        for rid, root_node in enumerate(root_list):
            if not root_node.is_show and len(root_node.scans) == 0:
                continue

            scan_stack = [root_node]
            sym_list = []
            while len(scan_stack):
                node = scan_stack.pop()
                if table_attr.view_type == 'tree':
                    try:
                        if node is root_node:
                            if is_virtual_en:
                                if did == last_did:
                                    sym = f"{ESYM}{did}:"
                                    sym_list.append("  ")
                                else:
                                    sym = f"{ISYM}{did}:"
                                    sym_list.append(BSYM)
                            else:
                                sym = ""
                        elif scan_stack[-1].level < node.level:
                            sym = "".join(sym_list+[ESYM])
                            if len(node.scans):
                                sym_list.append("  ")
                            else:
                                sym_lv = scan_stack[-1].level - node.level
                                sym_list = sym_list[:sym_lv]
                        else:
                            for idx in range(len(scan_stack)-1, -1, -1):
                                next_node = scan_stack[idx]
                                if (next_node.level == node.level
                                        and not next_node.is_hide):
                                    sym = "".join(sym_list+[ISYM])
                                    break
                                elif next_node.level < node.level:
                                    sym = "".join(sym_list+[ESYM])
                                    break
                            else:
                                sym = "".join(sym_list+[ESYM])

                            if len(node.scans):
                                sym_list.append(BSYM)
                    except Exception:
                        sym = "".join(sym_list+[ESYM])
                        if len(node.scans):
                            sym_list.append("  ")

                    if (table_attr.trace_root == 'sub'
                            and node.sr_name is not None):
                        path_name = "".join((sym, node.sr_name))
                    elif node.inst_name is None:
                        path_name = "".join((sym, node.bname))
                    else:
                        path_name = "".join((sym, node.inst_name))
                elif table_attr.view_type == 'inst':
                    if (table_attr.trace_root == 'sub'
                            and node.sr_name is not None):
                        path_name = node.sr_name
                    elif node.tag_name is not None:
                        path_name = node.tag_name
                    else:
                        if node.inst_name is not None:
                            path_name = node.inst_name
                        else:
                            path_name = node.bname

                        if is_multi:
                            path_name = f"{did}:{path_name}"
                else:
                    if (table_attr.trace_root == 'sub'
                            and node.sr_name is not None):
                        path_name = node.sr_name
                    elif node.tag_name is not None:
                        path_name = node.tag_name
                    else:
                        bname = (node.bname if node.inst_name is None
                                    else node.inst_name)
                        path_name = (bname if node.level < 2
                                        else f"{node.dname}/{bname}")
                        if is_multi:
                            if node.level > 0:
                                path_name = f"{root_node.bname}/{path_name}"
                            path_name = f"{did}:{path_name}"

                if table_attr.is_show_level:
                    if table_attr.trace_root == 'sub':
                        level = node.level - root_node.level
                    else:
                        level = node.level
                    path_name = '({}) {}'.format(str(level).rjust(lv_digi),
                                                 path_name)

                if node.gid_dict:
                    attr = "*"
                    for gid, sign in node.gid_dict.items():
                        sign = '+' if sign > 0 else '-'
                        attr += f"{gid}{sign}"
                else:
                    attr = ""

                if node.is_sub_sum:
                    comb_area = node.sub_comb_area
                    seq_area = node.sub_seq_area
                    bbox_area = node.sub_bbox_area
                else:
                    comb_area = node.comb_area
                    seq_area = node.seq_area
                    bbox_area = node.bbox_area

                atable.add_row(None, '', [
                    ','.join([node.dname, node.bname]),     # item
                    node.total_area,                        # total
                    comb_area,                              # comb
                    seq_area,                               # seq
                    bbox_area,                              # bbox
                    0.0,                                    # logic
                    0.0,                                    # ptotal
                    0.0,                                    # pbox
                    node.is_sub_sum,                        # sub_sum
                    not node.is_show,                       # hide
                    did,                                    # did
                    rid if node == root_node else None,     # rid
                    node.level,                             # level
                    attr,                                   # attr
                    path_name                               # name
                ])

                if table_attr.is_reorder:
                    scan_stack.extend(
                        sorted(node.scans, key=lambda x:x.total_area))
                else:
                    scan_stack.extend(
                        sorted(node.scans, key=lambda x:x.bname, reverse=True))

    root_total = 0.0
    for r in range(atable.max_row-1,-1,-1):
        atable[r,'total':'pbox'].align = [Align.TR] * 7
        if atable[r,'hide'].value:
            if table_attr.trace_root == 'leaf':
                atable.del_row(r)
            else:
                value = " - " if atable[r,'sub_sum'].value else "-"
                atable[r,'ptotal':'pbox'].value = [value] * 2
                atable[r,'ptotal':'pbox'].fs = ["{}"] * 2
        else:
            atable[r,'logic'].value = atable[r,'comb'] + atable[r,'seq']
            atable[r,'ptotal':'pbox'].fs = [perc_fs] * 2

            if table_attr.trace_root == 'sub':
                if atable[r,'rid'].value is not None:
                    atable[r,'name'].value = f"<{atable[r,'name'].value}>"
                    root_total = atable[r,'total'].value
                atable[r,'ptotal'].value = atable[r,'total'] / root_total
            else:
                atable[r,'ptotal'].value = atable[r,'total'] / vtotal

            if (hier_area:=atable[r,'logic']+atable[r,'bbox']) > 0:
                atable[r,'pbox'].value = atable[r,'bbox'] / hier_area
            else:
                atable[r,'pbox'].value = 0

    col_area_norm(atable, 'total', table_attr, is_hide_chk=True)
    for key in ('comb', 'seq', 'bbox', 'logic'):
        col_area_norm(atable, key, table_attr, is_sub_sum=is_sub_sum,
                      is_hide_chk=True)
    ## show area report ##

    unit = table_attr.unit

    area_t = virtual_top.total_area
    area_l = virtual_top.comb_area + virtual_top.seq_area
    area_b = virtual_top.bbox_area

    area_t2, fs = area_norm(area_t, table_attr)
    area_l2, *_ = area_norm(area_l, table_attr)
    area_b2, *_ = area_norm(area_b, table_attr)

    area_str_t = fs.format(area_t2)
    area_str_l = fs.format(area_l2).rjust(str_len:=len(area_str_t))
    area_str_b = fs.format(area_b2).rjust(str_len)

    print()
    print(f" Top Summary ".center(32, '='))
    print("  total: {} ({:>6.1%})".format(area_str_t, 1.0))
    print("  logic: {} ({:>6.1%})".format(area_str_l, area_l / area_t))
    print("   bbox: {} ({:>6.1%})".format(area_str_b, area_b / area_t))
    print("=" * 32)

    if table_attr.is_sub_sum:
        print("\n() : Sub-tree Area Summation")

    print(f"\nratio: {str(table_attr.ratio)}  unit: {unit.info}\n")

    ### update group table ###

    if gtable.max_row > 0:
        for r in range(gtable.max_row):
            gtable[r,'sub_sum'].value = True
            gtable[r,'logic'].value = gtable[r,'comb'] + gtable[r,'seq']

            if table_attr.trace_root == 'sub' and sub_root_cnt > 1:
                gtable[r,'ptotal'].value = 'NA'
                gtable[r,'ptotal'].fs = '{}'
            elif table_attr.trace_root == 'sub' and sub_root_cnt == 1:
                gtable[r,'ptotal'].value = gtable[r,'total'] / root_total
            else:
                gtable[r,'ptotal'].value = gtable[r,'total'] / vtotal

            if (hier_area:=gtable[r,'logic']+gtable[r,'bbox']) > 0:
                gtable[r,'pbox'].value = gtable[r,'bbox'] / hier_area
            else:
                gtable[r,'pbox'].value = 0

        col_area_norm(gtable, 'total', table_attr)
        gtable.set_col_attr('total', align=Align.TR)
        for key in ('comb', 'seq', 'bbox', 'logic'):
            col_area_norm(gtable, key, table_attr, is_sub_sum=is_sub_sum)
            gtable.set_col_attr(key, align=Align.TR)
        for key in ('ptotal', 'pbox'):
            gtable.set_col_attr(key, fs=perc_fs, align=Align.TR)

        size = max([len(x) for x in gtable.index.key])
        for key in gtable.index.key:
            gtable[key,'name'].value = \
                "{}: {}".format(key.rjust(size), gtable[key,'name'].value)

    ### sync column width ###

    if table_attr.view_type == 'path' and not table_attr.is_nosplit:
        plen = table_attr.path_col_size
        atable.set_col_attr('name', width=plen, is_sep=True)
    else:
        plen = atable.get_col_width('name')
        if plen < table_attr.path_col_size:
            plen = table_attr.path_col_size
            atable.set_col_attr('name', width=plen)

    if gtable.max_row > 0:
        glen = gtable.get_col_width('name')
        if glen > plen:
            plen = glen
            atable.set_col_attr('name', width=plen)
        else:
            gtable.set_col_attr('name', width=plen)

    for key in ('total', 'comb', 'seq', 'bbox', 'logic'):
        plen = atable.get_col_width(key)
        if plen < DEFAULT_AREA_COL_SIZE:
            atable.set_col_attr(key, width=(plen:=DEFAULT_AREA_COL_SIZE))
        if gtable.max_row > 0:
            glen = gtable.get_col_width(key)
            if glen > plen:
                plen = glen
                atable.set_col_attr(key, width=plen)
            else:
                gtable.set_col_attr(key, width=plen)

    ### print table ###

    hlist = ['name', 'total', 'ptotal']
    if not table_attr.is_brief:
        hlist += ['comb', 'seq'] if table_attr.is_logic_sep else ['logic']
        hlist += ['bbox', 'pbox']
    hlist += ['attr']

    atable.set_head_attr(border=Border(left=False,right=False))
    for r in range(ed:=atable.max_row-1):
        atable.set_row_attr(r, border=Border(left=False,right=False))
    if gtable.max_row > 0:
        atable.set_row_attr(ed, border=Border(left=False,right=False,
                                              bottom=False))
    else:
        atable.set_row_attr(ed, border=Border(left=False,right=False))

    atable.header['attr'].border = Border(top=False,bottom=False,
                                          left=False, right=False)
    for r in (0, atable.max_row-1):
        atable[r,'attr'].border = Border(top=False,bottom=False,
                                         left=False,right=False)
    atable.header['attr'].title = ""
    atable.print(column=hlist)

    if gtable.max_row > 0:
        gtable.set_head_attr(border=Border(left=False,right=False))
        for r in range(ed:=gtable.max_row-1):
            gtable.set_row_attr(r, border=Border(left=False,right=False))
        gtable.set_row_attr(ed, border=Border(left=False,right=False,
                                              bottom=False))
        gtable.print(column=hlist[:-1])
    else:
        print()


def show_bbox_area(design_db: DesignDB, table_attr: TableAttr):
    """Scan and show all black-box area"""

    ## backward trace from nodes with bbox

    virtual_top = design_db.virtual_top
    vtotal = virtual_top.total_area
    dslist = design_db.design_list
    is_sub_sum = table_attr.is_sub_sum
    area_fs = table_attr.area_fs
    perc_fs = "{:6.1%}"
    path_lv = 0

    is_multi = (last_did:=len(dslist)-1) > 0

    for design in dslist:
        for node in design.node_dict.values():
            if node is design.top_node and not is_multi:
                node.is_show = True
                node.sub_comb_area = design.comb_area
                node.sub_seq_area  = design.seq_area
                node.sub_bbox_area = design.bbox_area
                node.is_sub_sum = True
            elif node.bbox_area != 0:
                node.is_show = True
                if node.level > path_lv:
                    path_lv = node.level
                while True:
                    try:
                        node.parent.scans.add(node)
                        if len(node.parent.scans) > 1:
                            break
                        node = node.parent
                    except Exception:
                        break

    lv_digi = len(str(path_lv))
    table_attr.is_sub_sum = True

    ## create area table ##

    design_db.area_table = (atable:=SimpleTable(design_db.ahead))

    if table_attr.is_show_level:
        path_name = '({}) {}'.format('T'.rjust(lv_digi), virtual_top.top_node)
    else:
        path_name = f'{virtual_top.top_node}'

    if is_multi:
        atable.add_row(None, '', [
            'virtual_top',          # item
            virtual_top.total_area, # total
            virtual_top.comb_area,  # comb
            virtual_top.seq_area,   # seq
            virtual_top.bbox_area,  # bbox
            0.0,                    # logic
            0.0,                    # ptotal
            0.0,                    # pbox
            True,                   # sub_sum
            False,                  # hide
            None,                   # did
            None,                   # rid
            None,                   # level
            '',                     # attr
            path_name               # name
        ])

    for did, design in enumerate(dslist):
        scan_stack = [root_node:=design.top_node]
        sym_list = []
        while len(scan_stack):
            node = scan_stack.pop()
            if table_attr.view_type == 'tree':
                try:
                    if node is root_node:
                        if is_multi:
                            if did == last_did:
                                sym = f"{ESYM}{did}:"
                                sym_list.append("  ")
                            else:
                                sym = f"{ISYM}{did}:"
                                sym_list.append(BSYM)
                        else:
                            sym = ""
                    elif scan_stack[-1].level < node.level:
                        sym = "".join(sym_list+[ESYM])
                        if len(node.scans):
                            sym_list.append("  ")
                        else:
                            sym_list = \
                                sym_list[:scan_stack[-1].level-node.level]
                    else:
                        for idx in range(len(scan_stack)-1, -1, -1):
                            next_node = scan_stack[idx]
                            if next_node.level == node.level \
                                and not next_node.is_hide:
                                sym = "".join(sym_list+[ISYM])
                                break
                            elif next_node.level < node.level:
                                sym = "".join(sym_list+[ESYM])
                                break
                        else:
                            sym = "".join(sym_list+[ESYM])

                        if len(node.scans):
                            sym_list.append(BSYM)
                except Exception:
                    sym = "".join(sym_list+[ESYM])
                    if len(node.scans):
                        sym_list.append("  ")

                path_name = "".join((sym, node.bname))
            elif table_attr.view_type == 'inst':
                path_name = node.bname
                if is_multi:
                    path_name = f"{did}:{path_name}"
            else:
                if node.tag_name is not None:
                    path_name = node.tag_name
                else:
                    path_name = node.bname if node.level < 2 \
                                else f"{node.dname}/{node.bname}"
                    if is_multi:
                        if node.level > 0:
                            path_name = f"{root_node.bname}/{path_name}"
                        path_name = f"{did}:{path_name}"

            if table_attr.is_show_level:
                path_name = '({}) {}'.format(str(node.level).rjust(lv_digi),
                                             path_name)

            if node.is_sub_sum:
                comb_area = node.sub_comb_area
                seq_area = node.sub_seq_area
                bbox_area = node.sub_bbox_area
            else:
                comb_area = node.comb_area
                seq_area = node.seq_area
                bbox_area = node.bbox_area

            atable.add_row(None, '', [
                ','.join([node.dname, node.bname]),     # item
                node.total_area,                        # total
                comb_area,                              # comb
                seq_area,                               # seq
                bbox_area,                              # bbox
                0.0,                                    # logic
                0.0,                                    # ptotal
                0.0,                                    # pbox
                node.is_sub_sum,                        # sub_sum
                not node.is_show,                       # hide
                did,                                    # did
                None,                                   # rid
                node.level,                             # level
                '',                                     # attr
                path_name                               # name
            ])

            if table_attr.is_reorder:
                scan_stack.extend(
                    sorted(node.scans, key=lambda x:x.total_area))
            else:
                scan_stack.extend(
                    sorted(node.scans, key=lambda x:x.bname, reverse=True))

    root_total = 0.0
    for r in range(atable.max_row-1,-1,-1):
        atable[r,'total':'pbox'].align = [Align.TR] * 7
        if atable[r,'hide'].value:
            if table_attr.trace_root == 'leaf':
                atable.del_row(r)
            else:
                value = " - " if atable[r,'sub_sum'].value else "-"
                atable[r,'ptotal':'pbox'].value = [value] * 2
                atable[r,'ptotal':'pbox'].fs = ["{}"] * 2
        else:
            atable[r,'logic'].value = atable[r,'comb'] + atable[r,'seq']
            atable[r,'ptotal':'pbox'].fs = [perc_fs] * 2

            if table_attr.trace_root == 'sub':
                if atable[r,'rid'].value is not None:
                    atable[r,'name'].value = f"<{atable[r,'name'].value}>"
                    root_total = atable[r,'total'].value
                atable[r,'ptotal'].value = atable[r,'total'] / root_total
            else:
                atable[r,'ptotal'].value = atable[r,'total'] / vtotal

            if (hier_area:=atable[r,'logic']+atable[r,'bbox']) > 0:
                atable[r,'pbox'].value = atable[r,'bbox'] / hier_area
            else:
                atable[r,'pbox'].value = 0

    col_area_norm(atable, 'total', table_attr, is_hide_chk=True)
    for key in ('comb', 'seq', 'bbox', 'logic'):
        col_area_norm(atable, key, table_attr, is_sub_sum=is_sub_sum,
                      is_hide_chk=True)

    ## show area report ##

    unit = table_attr.unit
    area_fs = table_attr.area_fs

    area_t = virtual_top.total_area
    area_l = virtual_top.comb_area + virtual_top.seq_area
    area_b = virtual_top.bbox_area

    area_t2, fs = area_norm(area_t, table_attr)
    area_l2, *_ = area_norm(area_l, table_attr)
    area_b2, *_ = area_norm(area_b, table_attr)

    area_str_t = fs.format(area_t2)
    area_str_l = fs.format(area_l2).rjust(str_len:=len(area_str_t))
    area_str_b = fs.format(area_b2).rjust(str_len)

    print()
    print(f" Top Summary ".center(32, '='))
    print("  total: {} ({:>6.1%})".format(area_str_t, 1.0))
    print("  logic: {} ({:>6.1%})".format(area_str_l, area_l / area_t))
    print("   bbox: {} ({:>6.1%})".format(area_str_b, area_b / area_t))
    print("=" * 32)

    if table_attr.is_sub_sum:
        print("\n() : Sub-tree Area Summation")

    print(f"\nratio: {str(table_attr.ratio)}  unit: {unit.info}\n")

    if table_attr.view_type == 'path' and not table_attr.is_nosplit:
        plen = table_attr.path_col_size
        atable.set_col_attr('name', width=plen, is_sep=True)
    else:
        plen = atable.get_col_width('name')
        if plen < table_attr.path_col_size:
            plen = table_attr.path_col_size
            atable.set_col_attr('name', width=plen)

    for key in ('total', 'comb', 'seq', 'bbox', 'logic'):
        plen = atable.get_col_width(key)
        if plen < DEFAULT_AREA_COL_SIZE:
            atable.set_col_attr(key, width=(plen:=DEFAULT_AREA_COL_SIZE))

    ### print table ###

    hlist = ['name', 'total', 'ptotal']
    if not table_attr.is_brief:
        hlist += ['comb', 'seq'] if table_attr.is_logic_sep else ['logic']
        hlist += ['bbox', 'pbox']
    hlist += ['attr']

    atable.set_head_attr(border=Border(left=False,right=False))
    for r in range(ed:=atable.max_row-1):
        atable.set_row_attr(r, border=Border(left=False,right=False))
    atable.set_row_attr(ed, border=Border(left=False,right=False))
    atable.header['attr'].border = Border(top=False,bottom=False,
                                          left=False,right=False)
    for r in (0, atable.max_row-1):
        atable[r,'attr'].border = Border(top=False,bottom=False,
                                         left=False,right=False)
    atable.header['attr'].title = ""
    atable.print(column=hlist)
    print()


def show_divider(header_lens: list):
    """Show divider"""
    for length in header_lens:
        print('{}  '.format('-' * length), end='')
    print()


def show_header(header_lens: list, header_list: list):
    """Show header"""
    for i, head in enumerate(header_list):
        print("{}  ".format(head.split('/')[0].ljust(header_lens[i])), end='')
    print()

    try:
        for i, head in enumerate(header_list):
            print("{}  ".format(head.split('/')[1].ljust(header_lens[i])), end='')
        print()
    except:
        pass


def area_norm(value: float, table_attr: TableAttr) -> (float, str):
    """Return the normalize area and the f-string."""
    unit, org_fs = table_attr.unit, table_attr.area_fs
    unit_cnt = 0 if unit.type == UnitType.NONE else 1
    if unit.type == UnitType.SCI:
        while value >= unit.value:
            value /= unit.value
            unit_cnt += 1
    return value, f"{org_fs}{unit.tag*unit_cnt}"


def col_area_norm(table: SimpleTable, col_key, table_attr: TableAttr,
                  is_sub_sum: bool=False, is_hide_chk: bool=False):
    """Normalize area for the specific column and update the f-string."""
    for r in range(table.max_row):
        if is_hide_chk and table[r,'hide'].value:
            value = " - " if table[r,'sub_sum'].value else "-"
            table[r,col_key].value = value
            table[r,col_key].fs = "{}"
        else:
            table[r,col_key].value, fs = \
                area_norm(table[r,col_key].value, table_attr)
            if is_sub_sum:
                if table[r,'sub_sum'].value:
                    table[r,col_key].fs = f"({fs})"
                else:
                    table[r,col_key].fs = f" {fs} "
            else:
                table[r,col_key].fs = fs


### Main Function ###


def create_argparse() -> argparse.ArgumentParser:
    """Create Argument Parser"""
    parser = argparse.ArgumentParser(
                formatter_class=argparse.RawTextHelpFormatter,
                description="Design compiler area report analysis.")

    subparsers = parser.add_subparsers(dest='proc_mode',
                                       required=True,
                                       help="select one of process modes.")

    parser.add_argument('-version', action='version', version=VERSION)
    parser.add_argument('-dump', dest='dump_fn', metavar='<file>',
                                 help="dump leaf nodes in the list\n ")

    parser.add_argument('-ra', dest='ratio', metavar='<float>', type=float,
                               default=1.0, help="convert ratio")

    unit_gparser = parser.add_mutually_exclusive_group()
    unit_gparser.add_argument('-u1', dest='norm_unit', metavar='unit',
                                     choices=['k','K','w','W','m','M','b','B'],
                                     help="unit change (choices: [kKwWmMbB])")
    unit_gparser.add_argument('-u2', dest='sci_unit', metavar='unit',
                                     choices=['k','K','w','W','m','M','b','B'],
                                     help="scientific notation " + 
                                          "(choices: [kKwWmMbB])\n ")

    parser.add_argument('-dp', dest='dec_place', metavar='<int>', type=int,
                               default=4, 
                               help="number of decimal places of area")
    parser.add_argument('-ts', dest='is_show_ts', action='store_true',
                               help="show thousands separators")

    area_gparser = parser.add_mutually_exclusive_group()
    area_gparser.add_argument('-br', dest='is_brief', action='store_true',
                                     help="only show total area/percent value")
    area_gparser.add_argument('-ls', dest='is_logic_sep', action='store_true',
                                     help="show combi/non-combi area separately")

    parser.add_argument('-ro', dest='is_reorder', action='store_true',
                               help="area reorder (large first)")

    parser.add_argument('-lv', dest='is_show_level', action='store_true',
                               help="show hierarchical level")
    parser.add_argument('-ns', dest='is_nosplit', action='store_true',
                               help="cell path no-split\n ")

    path_gparser = parser.add_mutually_exclusive_group()
    path_gparser.add_argument('-t', dest='is_tree_view', action='store_true',
                                    help="show path with tree view")
    path_gparser.add_argument('-i', dest='is_inst_view', action='store_true',
                                    help="only show instance name " + 
                                         "(instance view)")

    # create the parser for normal mode
    parser_norm = subparsers.add_parser('norm', help='normal mode', 
                    formatter_class=argparse.RawTextHelpFormatter)
    parser_norm.add_argument('rpt_fn', nargs='+', help="area report path")
    parser_norm.add_argument('-vn', dest='vtop_name', metavar='<str>',
                                    type=str, default='VIRTUAL_TOP',
                                    help="virtual top name for multi-design in")

    # create the parser for advance mode
    parser_adv = subparsers.add_parser('adv', help='advance mode', 
                    formatter_class=argparse.RawTextHelpFormatter)
    parser_adv.add_argument('cfg_fn', help="configuration file")
    parser_adv.add_argument('rpt_fn', nargs='+', help="area report path")
    parser_adv.add_argument('-vn', dest='vtop_name', metavar='<str>',
                                   type=str, default='VIRTUAL_TOP',
                                   help="virtual top name for multi-design in")
    parser_adv.add_argument('-sr', dest='is_sub_trace', action='store_true',
                                   help="sub root backward trace")
    parser_adv.add_argument('-v', dest='is_verbose', action='store_true',
                                  help="show area of all trace nodes")

    # create the parser for black-box scan mode
    parser_bbox = subparsers.add_parser('bbox', help='black-box scan mode', 
                    formatter_class=argparse.RawTextHelpFormatter)
    parser_bbox.add_argument('rpt_fn', nargs='+', help="area report path")
    parser_bbox.add_argument('-vn', dest='vtop_name', metavar='<str>',
                                    type=str, default='VIRTUAL_TOP',
                                    help="virtual top name for multi-design in")

    return parser


def main():
    """Main Function"""
    parser = create_argparse()
    args = parser.parse_args()

    unit = UnitAttr()
    if args.norm_unit is not None:
        unit.type = UnitType.NORM
        unit.tag = args.norm_unit
    elif args.sci_unit is not None:
        unit.type = UnitType.SCI
        unit.tag = args.sci_unit

    match unit.tag.lower():
        case 'k':
            unit.value = pow(10, 3)
            unit.info = "1 thousand"
        case 'w':
            unit.value = pow(10, 4)
            unit.info = "10 thousand"
        case 'm':
            unit.value = pow(10, 6)
            unit.info = "1 million"
        case 'b':
            unit.value = pow(10, 9)
            unit.info = "1 billion"

    if args.proc_mode == 'adv' and args.is_sub_trace:
        trace_root = 'sub'
    else:
        trace_root = 'top' if args.is_tree_view else 'leaf'

    ts = ',' if args.is_show_ts else ''
    area_fs = f"{{:{ts}.{args.dec_place}f}}"

    table_attr = TableAttr(
                    area_fs=area_fs,
                    ratio=args.ratio,
                    unit=unit,
                    dec_place=args.dec_place,
                    is_show_ts=args.is_show_ts,
                    is_brief=args.is_brief,
                    is_logic_sep=args.is_logic_sep,
                    is_reorder=args.is_reorder,
                    is_show_level=args.is_show_level,
                    is_nosplit=args.is_nosplit,
                    view_type=('tree' if args.is_tree_view else
                               'inst' if args.is_inst_view else 'path'),
                    trace_root=trace_root,
                    proc_mode=args.proc_mode,
                    vtop_name=args.vtop_name)

    design_db = DesignDB()

    if args.proc_mode == 'adv':
        table_attr.is_verbose = args.is_verbose

    ## Main process

    design_db.virtual_top = (virtual_top:=Design(top_node=table_attr.vtop_name))
    design_db.design_list = (design_list:=load_area(args.rpt_fn, table_attr))

    if table_attr.proc_mode == 'adv':
        load_cfg(args.cfg_fn, design_db, table_attr)

    if len(design_list) > 1 and table_attr.trace_root != 'sub':
        table_attr.is_sub_sum = True    # for virtual top display

    for design in design_list:
        virtual_top.total_area += design.total_area
        virtual_top.comb_area += design.comb_area
        virtual_top.seq_area += design.seq_area
        virtual_top.bbox_area += design.bbox_area

        if design.max_lv >= virtual_top.max_lv:
            virtual_top.max_lv = design.max_lv

    if table_attr.proc_mode == 'norm' or table_attr.proc_mode == 'adv':
        show_hier_area(design_db, table_attr)
    elif table_attr.proc_mode == 'bbox':
        show_bbox_area(design_db, table_attr)

    if args.dump_fn is not None:
        with open(args.dump_fn, 'w') as f:
            scan_stack = [design.top_node]
            while len(scan_stack):
                node = scan_stack.pop()
                if len(node.scans) == 0:
                    path_name = "" if node.level < 2 else f"{node.dname}/"
                    path_name += node.bname
                    f.write(f"{path_name}\n")
                else:
                    scan_stack.extend(node.scans)


if __name__ == '__main__':
    main()


