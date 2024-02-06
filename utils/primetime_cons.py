# -*- coding: utf-8 -*-
# SPDX-License-Identifier: GPL-2.0-only
#
# Copyright (C) 2023 Yeh, Hsin-Hsien <yhh76227@gmail.com>
#
"""
Global Function for PrimeTime Report Analysis
"""
import copy
import gzip
import os
import re
from dataclasses import dataclass, field
from enum import IntEnum

import numpy as np
import pandas as pd


@dataclass (slots=True)
class ConsPathOp:
    re: re.Pattern = None
    l: list = field(default_factory=list)  # cmd: [fno, opteration]
    r: list = field(default_factory=list)
    def __getitem__(self, key):
        if key == 'l': return self.l
        if key == 'r': return self.r


@dataclass (slots=True)
class ConsGroupOp:
    re: re.Pattern = None
    l: list = field(default_factory=list)  # cmd: [fno, opteration]
    r: list = field(default_factory=list)
    d: list = field(default_factory=list)
    def __getitem__(self, key):
        if key == 'l': return self.l
        if key == 'r': return self.r
        if key == 'd': return self.d


@dataclass (slots=True)
class ConsUGroupOp:
    fno: int = 0
    re: re.Pattern = None
    ugroup: str = None
    is_rsv: bool = None


class ConsReport:
    """
    Constraint violation report parser.

    Variables
    ---------
    cons_tables  a list of constraint tables.
    """

    _path_hd = ('type', 'group', 'pin', 'sc', 'arr', 'req', 'slk', 'attr',
                'off', 'is_rsv', 'is_del', 'ugroup', 'i_ug_del')

    _sum_hd = ('group', 'l:wns', 'l:tns', 'l:nvp', 'r:wns', 'r:tns', 'r:nvp', 
               'd:wns', 'd:tns', 'd:nvp', 'comm')

    _cons_type_set = {
        'max_delay/setup', 'min_delay/hold', 'recovery', 'removal', 
        'clock_gating_setup', 'clock_gating_hold', 
        'max_capacitance', 'min_capacitance', 
        'max_transition', 'min_transition',
        'clock_tree_pulse_width', 'sequential_tree_pulse_width', 
        'sequential_clock_min_period'
    }

    _path_op = set(('r:slk', 'd:slk'))
    _group_op = set(('w:wns', 'w:tns', 'w:nvp'))

    _cmp_op = {
        '>' : lambda a, b: a > b,
        '<' : lambda a, b: a < b,
        '==': lambda a, b: a == b,
        '>=': lambda a, b: a >= b,
        '<=': lambda a, b: a <= b
    }

    def __init__(self, cons_cfg: dict):
        """
        Arguments
        ---------
        cons_cfg : the configuration dictionary.
        """
        self.update_cons_cfg(cons_cfg)
        self.cons_tables = []

    def update_cons_cfg(self, cons_cfg: dict):
        """
        Update configurations.

        Arguments
        ---------
        cons_cfg : the configuration dictionary.
        """
        self._grp_col_w = cons_cfg['grp_col_w']

        self._path_cfg = copy.deepcopy(cons_cfg['p'])
        for gtag, grp_dict in self._path_cfg.items():
            for ptag, path_obj in grp_dict.items():
                path_obj.path = re.compile(path_obj.path)
                if path_obj.l[0][0] == 0:
                    del path_obj.l[0]
                if path_obj.r[0][0] == 0:
                    del path_obj.r[0]
                for i, cmd in enumerate(path_obj.l):
                    path_obj.l[i] = (cmd[0], self._parse_path_cmd(cmd))
                for i, cmd in enumerate(path_obj.r):
                    path_obj.r[i] = (cmd[0], self._parse_path_cmd(cmd))
                grp_dict[ptag] = path_obj
            self._path_cfg[gtag] = grp_dict

        self._group_cfg = copy.deepcopy(cons_cfg['g'])
        for ttag, type_dict in self._group_cfg.items():
            for gtag, grp_obj in type_dict.items():
                grp_obj.group = re.compile(grp_obj.group)
                for i, cmd in enumerate(grp_obj.l):
                    grp_obj.l[i] = (cmd[0], self._parse_group_cmd(cmd))
                for i, cmd in enumerate(grp_obj.r):
                    grp_obj.r[i] = (cmd[0], self._parse_group_cmd(cmd))
                for i, cmd in enumerate(grp_obj.d):
                    grp_obj.d[i] = (cmd[0], self._parse_group_cmd(cmd))
                type_dict[gtag] = grp_obj
            self._group_cfg[ttag] = type_dict

        self._ugroup_cfg = copy.deepcopy(cons_cfg['ug'])
        for gtag, grp_dict in self._ugroup_cfg.items():
            for ptag, path_obj in grp_dict.items():
                path_obj.path = re.compile(path_obj.path)
                grp_dict[ptag] = path_obj
            self._ugroup_cfg[gtag] = grp_dict

    def _parse_path_cmd(self, cmd: tuple) -> tuple:
        no, op = cmd
        if op.startswith('s:'):
            return 's', float(op.split(':')[1])
        if op.startswith('r:') or op.startswith('d:'):
            op_list = re.fullmatch(r"(\w:\w{3})([><=]{1,2})(.+)", op)
            if op_list[1] not in self._path_op:
                raise SyntaxError(f"Error: config syntax error (ln:{no})")
            type_, tar = op_list[1].split(':')
            return type_, tar, op_list[2], float(op_list[3])
        if op == 'r' or op == 'd':
            return op, True
        raise SyntaxError(f"Error: config syntax error (ln:{no})")

    def _parse_group_cmd(self, cmd: tuple) -> tuple:
        no, op = cmd
        if op.startswith('w:'):
            op_list = re.fullmatch(r"(\w:\w{3})([><=]{1,2})(.+)", op)
            if op_list[1] not in self._group_op:
                raise SyntaxError(f"Error: config syntax error (ln:{no})")
            type_, tar = op_list[1].split(':')
            return type_, tar, op_list[2], float(op_list[3])
        raise SyntaxError(f"Error: config syntax error (ln:{no})")

    def parse_report(self, rpt_fps: list):
        """
        Parse the timing report.

        Arguments
        ---------
        rpt_fps : a list of the file path of constraint reports. (max number: 2)
        """
        st_idle, st_prefix, st_parsing = range(3)
        grp_re = re.compile(r"(?P<t>[\w\/]+)(?: +\('(?P<g>[\w\/]+)'\sgroup\))?")

        for fid, rpt_fp in enumerate(rpt_fps[:2]):
            if os.path.splitext(rpt_fp)[1] == '.gz':
                fp = gzip.open(rpt_fp, mode='rt')
            else:
                fp = open(rpt_fp)

            table = pd.DataFrame(np.full((128, len(self._path_hd)), np.NaN),
                                 columns=self._path_hd, dtype='object')
            self.cons_tables.append([0, table]) 

            stage, is_dmsa = st_idle, False
            line, fno = fp.readline(), 1
            while line:
                line = line.strip()
                if not (toks:=line.split()):
                    pass
                elif stage == st_idle and toks[0][0] == '*':
                    stage = st_prefix
                elif stage == st_prefix and toks[0][0] == '*':
                    stage = st_parsing
                elif stage == st_prefix and toks[0] == 'Design':
                    if toks[1] == 'multi_scenario':
                        is_dmsa = True
                elif stage == st_parsing:
                    m = grp_re.fullmatch(line)
                    if m and m['t'] in self._cons_type_set:
                        group = "" if m['g'] is None else m['g']
                        fno = self._parse_group(
                                fp, fid, fno, m['t'], group, is_dmsa)
                line, fno = fp.readline(), fno+1

            row_cnt, table = self.cons_tables[fid]
            if row_cnt < table.shape[0]:
                table = table.drop(range(row_cnt, table.shape[0]))
            self.cons_tables[fid][1] = table
            fp.close()

    def _parse_group(self, fp, fid: int, fno: int, gtype: str, group: str, 
                     is_dmsa: bool) -> int:
        """
        Parsing a violation group.

        Returns
        -------
        fno : the current line number of the report.
        """
        is_start, is_rec = False, False
        attr_re = re.compile(r"\(?(.*?)\)?")
        row_cnt = self.cons_tables[fid][0]
        table_v = self.cons_tables[fid][1].values
        content = []
        line, fno = fp.readline(), fno+1

        while line:
            toks = line.strip().split()
            if is_start:
                content.extend(toks)
                print(f"content: {content}")

            if not is_start:
                if toks and toks[0][0] == '-':
                    is_start = True
            elif not toks:
                break
            elif content[-1] == '(VIOLATED)':
                print("debug: check1")
                is_rec, cid = True, -2
            elif len(content) >= 2 and content[-2] == '(VIOLATED)':
                print("debug: check2")
                is_rec, cid = True, -3

            if is_rec:
                slk, cid = float(content[cid]), cid-1
                arr, cid = float(content[cid]), cid-1
                req, cid = float(content[cid]), cid-1 
                sc, cid = (content[cid], cid-1) if is_dmsa else ("", cid)
                attr = attr_re.fullmatch(' '.join(content[1:cid+1]))[1]
                pin = content[0]
                is_rec, content = False, []

                ## path config check
                off, is_rsv, is_del = 0.0, False, False
                for path_obj in self._path_cfg.get(group, {}).values():
                    if path_obj.path.fullmatch(pin):
                        rid = 'l' if fid == 0 else 'r'
                        for _, cmd in path_obj[rid]:
                            if cmd[0] == 's':
                                slk = slk + cmd[1]
                                off = cmd[1] 
                            elif cmd[0] == 'r':
                                if cmd[1] == True:
                                    is_rsv = True
                                else:
                                    is_rsv = self._cmp_op[cmd[2]](slk, cmd[3])
                            elif cmd[0] == 'd':
                                if cmd[1] == True:
                                    is_del = True
                                else:
                                    is_del = self._cmp_op[cmd[2]](slk, cmd[3])
                        break

                ## user group config check
                ugroup, is_ug_del = None, False
                for path_obj in self._ugroup_cfg.get(group, {}).values():
                    if path_obj.path.fullmatch(pin):
                        ugroup = path_obj.ugroup
                        is_ug_del = path_obj.is_ug_del
                        break

                table_v[row_cnt] = (
                    gtype, group, pin, sc, arr, req, slk, attr,
                    off, is_rsv, is_del, ugroup, is_ug_del)

                self.cons_tables[fid][0] = (row_cnt:=row_cnt+1)
                if (row_cnt & 127) == 0:
                    new = pd.DataFrame(
                            np.full((128, len(self._path_hd)), np.NaN),
                            columns=self._path_hd, dtype='object')
                    self.cons_tables[fid][1] = pd.concat(
                            [self.cons_tables[fid][1], new], ignore_index=True)
                    table_v = self.cons_tables[fid][1].values

            line, fno = fp.readline(), fno+1
        return fno

    def get_summary_table(self) -> pd.DataFrame:
        """
        Get summary table.

        Returns
        -------
        sum_table : the summary table.
        """
        pass
