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
from re import Pattern as RePat
from typing import Any

from simpletools.text import (Align, Array, Border, Index, SimpleTable)


@dataclass (slots=True)
class ConsPathOp:
    re: RePat = None
    l: list = field(default_factory=list)  # cmd: [fno, opteration]
    r: list = field(default_factory=list)
    def __getitem__(self, key):
        if key == 'l': return self.l
        if key == 'r': return self.r


@dataclass (slots=True)
class ConsGroupOp:
    re: RePat = None
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
    re: RePat = None
    ugroup: str = None
    is_og_rsv: bool = None


class ConsReport:
    """
    Constraint violation report parser.
    """

    _path_hd = (('type', 'Violation.Type'), ('group', 'Path.Group'), 
                ('pin', 'Pin'), ('sc', 'Scenario'), ('arr', 'Arrival.Time'), 
                ('req', 'Required.Time'), ('slk', 'Slack'), 
                ('attr', 'Attributes'), ('off', 'Slack.Offset'), 
                ('is_rsv', 'Reserve?'), ('is_del', 'Delete?'), 
                ('ugroup', 'User.Group'), 
                ('is_og_rsv', 'Original.Group.Reserve?'))

    _sum_hd = (('group', 'Group'), 
               ('lwns', 'WNS(L)'), ('ltns', 'TNS(L)'), ('lnvp', 'NVP(L)'),
               ('rwns', 'WNS(R)'), ('rtns', 'TNS(R)'), ('rnvp', 'NVP(R)'),
               ('dwns', 'WNS(D)'), ('dtns', 'TNS(D)'), ('dnvp', 'NVP(D)'),
               ('comm', ''))

    _grp_cons = ('max_delay/setup', 'min_delay/hold')
    _nogrp_cons = ('recovery', 'removal', 
                   'clock_gating_setup', 'clock_gating_hold', 
                   'max_capacitance', 'min_capacitance', 
                   'max_transition', 'min_transition')
    _clk_cons = ('clock_tree_pulse_width', 'sequential_tree_pulse_width', 
                 'sequential_clock_min_period')

    _cons_type_set = set(_grp_cons + _nogrp_cons + _clk_cons)

    _path_op = {'r:slk', 'd:slk'}
    _group_op = {'w:wns', 'w:tns', 'w:nvp'}

    _cmp_op = {
        '>' : lambda a, b: a > b,
        '<' : lambda a, b: a < b,
        '==': lambda a, b: a == b,
        '>=': lambda a, b: a >= b,
        '<=': lambda a, b: a <= b
    }

    def __init__(self, gcol_w: int=0, path_cfg: dict=None, grp_cfg: dict=None, 
                 ugrp_cfg: dict=None):
        """
        Parameters
        ----------
        gcol_w : int, optional
            The column width of the path group column.
        path_cfg : dict, optional
            Configurations for paths.
        grp_cfg : dict, optional
            Configurations for path groups.
        ugrp_cfg : dict, optional
            Configurations for user-defined path groups.
        """
        ### attributes
        self.gcol_w = gcol_w
        self.path_cfg = {} if path_cfg is None else copy.deepcopy(path_cfg)
        self.grp_cfg = {} if grp_cfg is None else copy.deepcopy(grp_cfg)
        self.ugrp_cfg = {} if ugrp_cfg is None else copy.deepcopy(ugrp_cfg)
        self._parse_cfg_cmd()
        ### data
        self.cons_tables = []
        self.sum_tables = {}

    def _parse_cfg_cmd(self):
        """
        Parsing config commands.
        """
        for gtag, gdict in self.path_cfg.items():
            for ptag, pobj in gdict.items():
                for i, cmd in enumerate(pobj.l):
                    pobj.l[i] = (cmd[0], self._parse_path_cmd(cmd))
                for i, cmd in enumerate(pobj.r):
                    pobj.r[i] = (cmd[0], self._parse_path_cmd(cmd))

        for ttag, tdict in self.grp_cfg.items():
            for gtag, gobj in tdict.items():
                for i, cmd in enumerate(gobj.l):
                    gobj.l[i] = (cmd[0], self._parse_group_cmd(cmd))
                for i, cmd in enumerate(gobj.r):
                    gobj.r[i] = (cmd[0], self._parse_group_cmd(cmd))
                for i, cmd in enumerate(gobj.d):
                    gobj.d[i] = (cmd[0], self._parse_group_cmd(cmd))

    def _parse_path_cmd(self, cmd: tuple[str, str]) -> tuple[Any, ...]:
        """
        Parsing config commands (path).
        """
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

    def _parse_group_cmd(self, cmd: tuple[str, str]) -> tuple[Any, ...]:
        """
        Parsing config commands (path group).
        """
        no, op = cmd
        if op.startswith('w:'):
            op_list = re.fullmatch(r"(\w:\w{3})([><=]{1,2})(.+)", op)
            if op_list[1] not in self._group_op:
                raise SyntaxError(f"Error: config syntax error (ln:{no})")
            type_, tar = op_list[1].split(':')
            return type_, tar, op_list[2], float(op_list[3])
        raise SyntaxError(f"Error: config syntax error (ln:{no})")

    def parse_report(self, rpt_fps: list[str]):
        """
        Parse the timing report.

        Parameters
        ----------
        rpt_fps : list[str]
            A list of the file path of constraint reports. (max number: 2)
        """
        st_idle, st_prefix, st_parsing = range(3)
        grp_re = re.compile(r"(?P<t>[\w\/]+)(?:\s+\('(?P<g>[\w\/]+)'\sgroup\))?")

        for fid, rpt_fp in enumerate(rpt_fps[:2]):
            if os.path.splitext(rpt_fp)[1] == '.gz':
                fp = gzip.open(rpt_fp, mode='rt')
            else:
                fp = open(rpt_fp)

            table = SimpleTable(self._path_hd)
            self.cons_tables.append(table) 

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
            fp.close()

        self._update_sum_table()

    def _parse_group(self, fp, fid: int, fno: int, gtype: str, group: str, 
                     is_dmsa: bool) -> int:
        """
        Parsing a violation group.

        Parameters
        ----------
        fp : file
            File point of the report.
        fid : int
            File id of the report.
        fno : int
            Current line number of the report (before parsing).
        gtype : str    
            Constraint type.
        group : str
            Path group name
        is_dmsa : bool 
            If current report is a DMSA report?

        Returns
        -------
        fno : int
            Current line number of the report (after parsing).
        """
        is_start, is_rec = False, False
        table = self.cons_tables[fid]
        content = []
        line, fno = fp.readline(), fno+1

        while line:
            toks = line.strip().split()
            if is_start:
                content.extend(toks)
            if not is_start:
                if toks and toks[0][0] == '-':
                    is_start = True
            elif not toks:
                break
            elif content[-1] == '(VIOLATED)':
                is_rec, cid, is_pulse_chk = True, -2, False
            elif len(content) >= 2 and content[-2] == '(VIOLATED)':
                is_rec, cid, is_pulse_chk = True, -3, True

            if is_rec:
                slk, cid = float(content[cid]), cid-1
                arr, cid = float(content[cid]), cid-1
                req, cid = float(content[cid]), cid-1 
                sc, cid = (content[cid], cid-1) if is_dmsa else ("", cid)
                if is_pulse_chk:
                    pulse_type = ' '.join(content[1:cid+1])[1:-1].split()[-1]
                    attr = f"{content[-1]},{pulse_type}"
                else:
                    attr = ''
                pin = content[0]
                is_rec, content = False, []
                key1 = f"{gtype}:{group}"
                key2 = f"{gtype}:"

                ## path config check
                # import pdb; pdb.set_trace()
                off, is_rsv, is_del = 0.0, False, False
                for pobj in (list(self.path_cfg.get(key1, {}).values()) + 
                             list(self.path_cfg.get(key2, {}).values())):
                    if pobj.re.fullmatch(pin):
                        rid = 'l' if fid == 0 else 'r'
                        for _, cmd in pobj[rid]:
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
                ugroup, is_og_rsv = None, False
                for pobj in (list(self.ugrp_cfg.get(key1, {}).values()) +
                             list(self.ugrp_cfg.get(key2, {}).values())):
                    if pobj.re.fullmatch(pin):
                        ugroup = pobj.ugroup
                        is_og_rsv = pobj.is_og_rsv
                        break

                table.add_row(None, '', 
                    [gtype, group, pin, sc, arr, req, slk, attr, off, 
                     is_rsv, is_del, ugroup, is_og_rsv])

            line, fno = fp.readline(), fno+1
        return fno

    def _update_sum_table(self):
        """
        Update summary table.
        """
        stable = self.sum_tables
        hid = None
        # ctable.print()
        # import pdb; pdb.set_trace()
        ##bookmark

        for rid in range(rlen:=len(self.cons_tables)):
            ctable = self.cons_tables[rid]
            for r in range(ctable.max_row):
                if (ptype:=ctable[r,'type']) not in stable:
                    border = Border(False, False, False, False) if rlen == 1 \
                                else Border(True, False, False, False)
                    gtable = SimpleTable(heads=self._sum_hd,
                                         border=border,
                                         lsh=2, hpat='=', hcpat='=', 
                                         cpat_alon=True)
                    # gtable.set_head_attr(border=Border(left=False, right=False))

                    if hid is None:
                        hid = gtable.header.id

                    gtable.header[hid['comm']].border = \
                        Border(False, False, False, False)
                    gtable.set_col_attr(hid['group'], width=self.gcol_w)

                    if rlen > 1:
                        for key in ('lwns', 'ltns', 'rwns', 'rtns', 
                                    'dwns', 'dtns'):
                            gtable.set_col_attr(hid[key], width=16)
                        for key in ('lnvp', 'rnvp', 'dnvp'):
                            gtable.set_col_attr(hid[key], width=6)
                        for key in ('lwns', 'rwns', 'dwns'):
                            gtable.header[hid[key]].border.left = True
                        for key in ('lnvp', 'rnvp', 'dnvp'):
                            gtable.header[hid[key]].border.right = True
                    else:
                        for key in ('lwns', 'ltns'):
                            gtable.set_col_attr(hid[key], width=16)
                        for key in ('lnvp',):
                            gtable.set_col_attr(hid[key], width=6)

                    stable[ptype] = gtable
                else:
                    gtable = stable[ptype]

                pgroup = ptype if ptype in self._nogrp_cons \
                            else ctable[r,'attr'] if ptype in self._clk_cons \
                            else ctable[r,'group']

                is_del = ctable[r,'is_del'] and not ctable[r,'is_rsv']
                slk = 0.0 if is_del else ctable[r,'slk']
                cnt = 0 if is_del else 1
                rkey = f'{ptype}:{pgroup}'

                if gtable.max_row == 0 or rkey not in gtable.index.id:
                    gtable.add_row(
                        key=rkey, title='', 
                        data=[pgroup, slk, slk, cnt, 0, 0, 0, 0, 0, 0],
                        )
                        #border=Border(False, False, False, False))
                    gtable.attr[-1, hid['comm']].border = \
                        Border(False, False, False, False)
                    if rlen > 1:
                        for ckey in ('lwns', 'ltns', 'rwns', 'rtns', 
                                    'dwns', 'dtns'):
                            gtable.attr[-1,hid[ckey]].fs = '{:.4f}'
                    else:
                        for ckey in ('lwns', 'ltns'):
                            gtable.attr[-1,hid[ckey]].fs = '{:.4f}'
                else:
                    if rid == 0:
                        if slk < gtable[rkey, hid['lwns']]:
                            gtable[rkey,hid['lwns']] = slk
                        gtable[rkey, hid['ltns']] += slk
                        gtable[rkey, hid['lnvp']] += cnt 
                    else:
                        if slk < gtable[rkey, hid['rwns']]:
                            gtable[rkey, hid['rwns']] = slk
                        gtable[rkey, hid['rtns']] += slk
                        gtable[rkey, hid['rnvp']] += cnt 

        if rlen == 1:
            for table in stable.values():
                for key in ('lwns', 'ltns', 'lnvp'):
                    title = table.header[hid[key]].title
                    table.header[hid[key]].title = title[:-3]
        # else:
        #     for table in stable.values():
        #         for r in 


