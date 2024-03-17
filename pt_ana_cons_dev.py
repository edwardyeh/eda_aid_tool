#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# SPDX-License-Identifier: GPL-2.0-only
#
# PrimeTime Report Analysis
# -- Summary of report_constraint
# -- command: report_cons -all_vio -path end
#
# Copyright (C) 2023 Yeh, Hsin-Hsien <yhh76227@gmail.com>
#
import argparse
import gzip
import os
import re

from .utils.common import PKG_VERSION, PT_CONS_VER
from .utils.primetime_cons import (ConsPathOp, ConsGroupOp, ConsUGroupOp, 
                                   ConsReport)

VERSION = f"pt_ana_cons version {PT_CONS_VER} ({PKG_VERSION})"


### Global Variable ###

# ofs_re = re.compile(r"(\w:)(.+)")
# ofs_ta = set(('s:',))

cmp_re = re.compile(r"(\w:\w{3})([><=]{1,2})(.+)")
cmp_ta = set(('w:wns', 'w:tns', 'w:nvp', 'r:slk', 'd:slk'))

# clk_vio = (
#     'clock_tree_pulse_width', 
#     'sequential_tree_pulse_width', 
#     'sequential_clock_min_period'
# )

# group_vio = ('max_delay/setup', 'min_delay/hold')


##############################################################################
### Function


def load_cons_cfg(cfg_fp) -> dict:
    """
    Load configurations from the file to database.

    Parameters
    ----------
    cfg_fp : file point
        File point of the config file.

    Returns
    -------
    cons_cfg : dict
        The config dictionary base on the config data structure.

    Notes
    -----

    Config Data Structure:
    
        cons_cfg = {
          'p': {'type1:group1': {path1: path_obj1, path2: path_obj2, ...}, 
                'type2:*':      {path3: path_obj3, path4: path_obj4, ...},
                  ... },
        
          'g': {'type1': {group1: group_obj1, group2: group_obj2, ...},
                'type2': {group3: group_obj3, group4: group_obj4, ...},
                  ... },
        
          'ug': {'type1:group1': {path1: path_obj1, path2: path_obj2, ...}, 
                 'type2:*':      {path3: path_obj3, path4: path_obj4, ...},
                  ... },
        }

    """
    attr = {
        'group_column_width': ('gcol_w', 50)
    }

    cons_cfg = dict(attr.values())
    cons_cfg.update({
        'p': {}, 'g': {}, 'ug': {}
    })

    if cfg_fp is None:
        return cons_cfg

    with open(cfg_fp, 'r') as fp:
        for fno, line in enumerate(fp, 1):
            if (line:=line.split('#')[0].strip()):
                try:
                    key, value, *_ = line.split(':')
                    key, value = key.strip(), value.strip()
                    if key in attr:
                        key2, df_val = attr[key]
                        if (ktype:=type(df_val)) is bool:
                            if value.lower() == str(not df_val).lower():
                                cons_cfg[key2] = not df_val
                            else:
                                cons_cfg[key2] = df_val
                        elif ktype is int:
                            cons_cfg[key2] = int(value)
                        elif ktype is float:
                            cons_cfg[key2] = float(value)
                        else:
                            raise SyntaxError(
                                f"Attributes - unsupported data type ({ktype}).")
                    elif key == 'p':
                        tag, *cmd_src = line[2:].split()
                        type_, group, path, rid = tag.split(':')
                        gid = ':'.join((type_, group))
                        pdict = cons_cfg['p'].setdefault(gid, {})
                        path_obj = pdict.setdefault(
                                path, ConsPathOp(re=re.compile(path), 
                                                 l=[(0, 's:0.0')], 
                                                 r=[(0, 's:0.0')]))
                        for cmd in cmd_src:
                            if rid in {'l', 'a'}:
                                if cmd.startswith('s'):
                                    path_obj.l[0] = (fno, cmd)
                                else:
                                    path_obj.l.append((fno, cmd))
                            if rid == 'r' or rid == 'a':
                                if cmd.startswith('s'):
                                    path_obj.r[0] = (fno, cmd)
                                else:
                                    path_obj.r.append((fno, cmd))
                    elif key == 'g':
                        tag, *cmd_src = line[2:].split()
                        type_, group, rid = tag.split(':')
                        gdict = cons_cfg['g'].setdefault(type_, {})
                        grp_obj = gdict.setdefault(
                                    group, ConsGroupOp(re=re.compile(group)))
                        for cmd in cmd_src:
                            grp_obj[rid].append((fno, cmd))
                    elif key == 'ug':
                        tag, cmd = line[3:].split()
                        type_, group, path = tag.split(':')
                        gid = ':'.join((type_, group))
                        ugdict = cons_cfg['ug'].setdefault(gid, {})
                        ugroup, is_rsv = cmd.split(':')
                        is_rsv = True if is_rsv.lower() == 'y' else False
                        ugdict[path] = ConsUGroupOp(fno=fno,
                                                    re=re.compile(path),
                                                    ugroup=ugroup,
                                                    is_og_rsv=is_rsv)
                except SyntaxError:
                    raise SyntaxError(f"config syntax error (ln:{fno})")

    for gtag, grp_dict in cons_cfg['p'].items():
        for ptag, path_obj in grp_dict.items():
            if path_obj.l[0][0] == 0:
                del path_obj.l[0]
            if path_obj.r[0][0] == 0:
                del path_obj.r[0]

    # import pdb; pdb.set_trace()  # debug
    return cons_cfg


def parse_grp_cmd(ln_no: int, grp_list: list, cmd_list: list):
    """Parse group command"""  #{{{
    idx = 0
    while idx < len(cmd_list):
        cmd = cmd_list[idx]
        idx = idx + 1

        if cmd == '':
            continue
        elif cmd.startswith('w'):
            m = cmp_re.fullmatch(cmd)
            if m is None or m[1] not in cmp_ta:
                raise SyntaxError('PGC-001')
            else:
                grp_list.append((ln_no, m[1], m[2], float(m[3])))
#}}}

def grp_cons_check(rid: int, values: list, cons_list: list, comm: str, cond_set: set) -> str:
    """Group Config Check"""  #{{{
    for cons in cons_list:
        if cons[1] == 'w:wns':
            opd_a = values[0]
        elif cons[1] == 'w:tns':
            opd_a = values[1]
        elif cons[1] == 'w:nvp':
            opd_a = values[2]

        if cmp_op[cons[2]](opd_a, cons[3]):
            cid = cons[1][0] + str(cons[0])
            comm += f"{cid},"
            if rid is None:
                cond_set.add("{0:8}{1[1]}{1[2]}{1[3]}".format(f"{cid}:", cons))
            else:
                cond_set.add("{0:8}{1}:{2[1]}{2[2]}{2[3]}".format(f"{cid}:", rid, cons))

    return comm
#}}}

def parse_ins_cmd(ins_list: list, cmd_list: list):
    """Parse instance command"""  #{{{
    idx = 0
    while idx < len(cmd_list):
        cmd = cmd_list[idx]
        idx = idx + 1

        if cmd == '':
            continue

        elif cmd == 'r' or cmd == 'd':
            ins_list.append(cmd)

        elif cmd.startswith('s'):
            m = ofs_re.fullmatch(cmd)
            if m is None or m[1] not in ofs_ta:
                raise SyntaxError('PIC-001')
            else:
                ins_list.append((m[1], float(m[2])))

        elif cmd.startswith('r') or cmd.startswith('d'):
            m = cmp_re.fullmatch(cmd)
            if m is None or m[1] not in cmp_ta:
                raise SyntaxError('PIC-002')
            else:
                ins_list.append((m[1], m[2], float(m[3])))
#}}}

def ins_cons_check(slack: float, cons_list: list) -> (bool, float):
    """Instance Config Check"""  #{{{
    off, is_active, is_rsv, is_del = 0.0, False, False, False
    rsv_slk, del_slk = (False, None), (False, None)

    for cons in cons_list:
        if cons[0] == 's:':
            off = float(cons[1])
        elif cons[0] == 'r':
            is_rsv = True
        elif cons[0] == 'r:slk':
            rsv_slk = True, cons
        elif cons[0] == 'd':
            is_del = True
        elif cons[0] == 'd:slk':
            del_slk = True, cons

    if not is_rsv and rsv_slk[0]:
        is_rsv = cmp_op[rsv_slk[1][1]](slack, rsv_slk[1][2])
    if not is_del and del_slk[0]:
        is_del = cmp_op[del_slk[1][1]](slack, del_slk[1][2])

    is_active = not is_del or is_rsv
    slack += off

    return is_active, slack
#}}}


def report_cons_summary(rpt_fps: list, cfg_fp: str):
    """
    Report the summary of the command 'report_constraint'
    """
    cons_cfg = load_cons_cfg(cfg_fp)
    cons_rpt = ConsReport(gcol_w=cons_cfg['gcol_w'],
                          path_cfg=cons_cfg['p'],
                          grp_cfg=cons_cfg['g'],
                          ugrp_cfg=cons_cfg['ug'])

    cons_rpt.parse_report(rpt_fps)

    tnum = len(cons_rpt.cons_tables)
    for i in range(tnum):
        print(f"==== Table {i}")
        cons_rpt.cons_tables[i].print()

    for type_, table in cons_rpt.sum_tables.items():
        print(f"==== {type_}")
        if tnum == 1:
            table.print(column=['group', 
                                'lwns', 'ltns', 'lnvp',
                                'comm'])
        else:
            table.print(column=['group', 
                                'lwns', 'ltns', 'lnvp',
                                'rwns', 'rtns', 'rnvp',
                                'dwns', 'dtns', 'dnvp', 
                                'comm'])
        print()

    import pdb;pdb.set_trace()
    # print(cons_rpt.cons_tables[0][1])

    IDLE, POS, VT1, VT2 = range(4)
    is_multi = len(rpt_fps) > 1
    stage, summary = IDLE, {}

    # for fid, rpt_fp in enumerate(rpt_fps):
    #     if os.path.splitext(rpt_fp)[1] == '.gz':
    #         f = gzip.open(rpt_fp, mode='rt')
    #     else:
    #         f = open(rpt_fp)

    #     for line in f:
    #         toks = line.split()
    #         toks_len = len(toks)

    #         if stage == IDLE and toks_len != 0 and toks[0] in vio_types:
    #             stage, vtype, wns, tns, nvp = POS, toks[0], 0.0, 0.0, 0
    #             group = toks[1][2:-1] if vtype in group_vio else vtype
    #             item = []

    #         elif stage == POS and toks_len != 0:
    #             if toks[0].startswith('---'):
    #                 vtype_dict = summary.setdefault(vtype, {})
    #                 if vtype in clk_vio and pre_toks[-1] == 'Clock':
    #                     stage = VT2
    #                     group = ""
    #                 else:
    #                     stage = VT1 
    #                     if is_multi:
    #                         group_list = vtype_dict.setdefault(group, [(0.0, 0.0, 0), (0.0, 0.0, 0)])
    #                     else:
    #                         group_list = vtype_dict.setdefault(group, [(0.0, 0.0, 0)])
    #             else:
    #                 pre_toks = toks.copy()

    #         elif stage == VT1:
    #             ## type: <endpoint> [scenario] <required delay> <actual delay> <slack>
    #             if toks_len != 0:
    #                 item.extend(toks)
    #                 if item[-1] == '(VIOLATED)':
    #                     is_active, slack = True, float(item[-2])
    #                     if len(cons_cfg['p']) != 0:
    #                         tag = f'{vtype}:{group}:{item[0]}'
    #                         if is_active and tag in cons_cfg['p']:
    #                             is_active, slack = ins_cons_check(slack, cons_cfg['p'][tag][fid])
    #                         tag = f'{vtype}::{item[0]}'
    #                         if is_active and tag in cons_cfg['p']:
    #                             is_active, slack = ins_cons_check(slack, cons_cfg['p'][tag][fid])
    #                         tag = f'{vtype}:{group}:'
    #                         if is_active and tag in cons_cfg['p']:
    #                             for ipat, inst_list in cons_cfg['p'][tag].items():
    #                                 if re.fullmatch(ipat, item[0]):
    #                                     is_active, slack = ins_cons_check(slack, inst_list[fid])
    #                                     break
    #                         tag = f'{vtype}::'
    #                         if is_active and tag in cons_cfg['p']:
    #                             for ipat, inst_list in cons_cfg['p'][tag].items():
    #                                 if re.fullmatch(ipat, item[0]):
    #                                     is_active, slack = ins_cons_check(slack, inst_list[fid])
    #                                     break
    #                     if is_active:
    #                         tns += slack 
    #                         nvp += 1
    #                         if slack < wns:
    #                             wns = slack
    #                     item = []
    #             else:
    #                 group_list[fid] = (wns, tns, nvp)
    #                 stage = IDLE

    #         elif stage == VT2:
    #             ## type: <endpoint> [scenario] <required delay> <actual delay> <slack> <clock>
    #             if toks_len != 0:
    #                 item.extend(toks)
    #                 if item[-2] == '(VIOLATED)':
    #                     if group != item[-1]:
    #                         if group != "":
    #                             group_list[fid][0] += wns
    #                             group_list[fid][1] += tns
    #                             group_list[fid][2] += nvp
    #                             wns, tns, nvp = 0.0, 0.0, 0
    #                         group = item[-1]

    #                         if is_multi:
    #                             group_list = vtype_dict.setdefault(group, [[0.0, 0.0, 0], [0.0, 0.0, 0]])
    #                         else:
    #                             group_list = vtype_dict.setdefault(group, [[0.0, 0.0, 0]])

    #                     is_active, slack = True, float(item[-3])

    #                     if len(cons_cfg['p']) != 0:
    #                         tag = f'{vtype}:{group}:{item[0]}'
    #                         if is_active and tag in cons_cfg['p']:
    #                             is_active, slack = ins_cons_check(slack, cons_cfg['p'][tag][fid])
    #                         tag = f'{vtype}::{item[0]}'
    #                         if is_active and tag in cons_cfg['p']:
    #                             is_active, slack = ins_cons_check(slack, cons_cfg['p'][tag][fid])
    #                         tag = f'{vtype}:{group}:'
    #                         if is_active and tag in cons_cfg['p']:
    #                             for ipat, inst_list in cons_cfg['p'][tag].items():
    #                                 if re.fullmatch(ipat, item[0]):
    #                                     is_active, slack = ins_cons_check(slack, inst_list[fid])
    #                                     break
    #                         tag = f'{vtype}::'
    #                         if is_active and tag in cons_cfg['p']:
    #                             for ipat, inst_list in cons_cfg['p'][tag].items():
    #                                 if re.fullmatch(ipat, item[0]):
    #                                     is_active, slack = ins_cons_check(slack, inst_list[fid])
    #                                     break
    #                     if is_active:
    #                         tns += slack 
    #                         nvp += 1
    #                         if slack < wns:
    #                             wns = slack
    #                     item = []
    #             else:
    #                 group_list[fid][0] += wns
    #                 group_list[fid][1] += tns
    #                 group_list[fid][2] += nvp
    #                 stage = IDLE

    #     f.close()

    if True:
        print()
        if is_multi:
            print("Report(left):  {}".format(os.path.abspath(rpt_fps[0])))
            print("Report(right): {}".format(os.path.abspath(rpt_fps[1])))
            print()
            print("Information:   Diff = Left - Right")
        else:
            print("Report:  {}".format(os.path.abspath(rpt_fps[0])))
        print()

        cond_set = set()
        for vtype, vtype_dict in summary.items():
            eq_cnt = gcol_w + 40
            print("==== {}".format(vtype))
            if is_multi:
                eq_cnt += 80
                print("  {}+{:=^39}+{:=^39}+{:=^39}+".format('=' * gcol_w, ' Left ', ' Right ', ' Diff '))
                print("  {}".format('Group'.ljust(gcol_w)), end='')
                print("| {:16}{:16}{:6}".format('WNS', 'TNS', 'NVP'), end='')
                print("| {:16}{:16}{:6}".format('WNS', 'TNS', 'NVP'), end='')
                print("| {:16}{:16}{:6}".format('WNS', 'TNS', 'NVP'), end='')
                print("|")
                print('  ', '=' * eq_cnt, '+', sep='')

                for group, group_list in vtype_dict.items():
                    comm, tag1, tag2 = '', f'{vtype}:{group}', f'{vtype}:'
                    print("  {}".format(group.ljust(gcol_w)), end='')
                    for rid, values in enumerate(group_list):
                        print("| {0[0]:< 16.4f}{0[1]:< 16.4f}{0[2]:<6}".format(values), end='')
                        if tag1 in cons_cfg['g']:
                            comm = grp_cons_check(rid, values, cons_cfg['g'][tag1][rid], comm, cond_set)
                        if tag2 in cons_cfg['g']:
                            for gpat, gcons_list in cons_cfg['g'][tag2].items():
                                if re.fullmatch(gpat, group):
                                    comm = grp_cons_check(rid, values, gcons_list[rid], comm, cond_set)

                    diff_values = [group_list[0][0] - group_list[1][0]]
                    diff_values.append(group_list[0][1] - group_list[1][1])
                    diff_values.append(group_list[0][2] - group_list[1][2])
                    print("| {0[0]:<+16.4f}{0[1]:<+16.4f}{0[2]:<+6}|".format(diff_values), end='')

                    if tag1 in cons_cfg['g']:
                        comm = grp_cons_check(2, diff_values, cons_cfg['g'][tag1][2], comm, cond_set)
                    if tag2 in cons_cfg['g']:
                        for gpat, gcons_list in cons_cfg['g'][tag2].items():
                            if re.fullmatch(gpat, group):
                                comm = grp_cons_check(2, diff_values, gcons_list[2], comm, cond_set)
                    if comm != '':
                        print(f" ({comm[:-1]})")
                    else:
                        print()
            else:
                print("  {}  {:16}{:16}{:6}".format('Group'.ljust(gcol_w), 'WNS', 'TNS', 'NVP'))
                print('  ', '=' * eq_cnt, sep='')
                for group, group_list in vtype_dict.items():
                    values = group_list[0]
                    print("  {}".format(group.ljust(gcol_w)), end='')
                    print("  {0[0]:< 16.4f}{0[1]:< 16.4f}{0[2]:<6}".format(values), end='')

                    comm, tag = '', f'{vtype}:{group}'
                    if tag in cons_cfg['g']:
                        comm = grp_cons_check(None, values, cons_cfg['g'][tag][0], comm, cond_set)
                    tag = f'{vtype}:'
                    if tag in cons_cfg['g']:
                        for gpat, gcons_list in cons_cfg['g'][tag].items():
                            if re.fullmatch(gpat, group):
                                comm = grp_cons_check(None, values, gcons_list[0], comm, cond_set)
                    if comm != '':
                        print(f" ({comm[:-1]})")
                    else:
                        print()
            print()

        if len(cond_set) != 0:
            print("\n[Condition]\n")
            for cond in cond_set:
                print(f"  {cond}")
            print()


##############################################################################
### Main


def create_argparse() -> argparse.ArgumentParser:
    """Create Argument Parser"""
    parser = argparse.ArgumentParser(
                formatter_class=argparse.RawTextHelpFormatter,
                description="PrimeTime Report Analysis\n" + 
                            "-- Summary of report_constraint\n" +
                            "-- command: report_cons -all_vio -path end")

    parser.add_argument('-version', action='version', version=VERSION)
    parser.add_argument('rpt_fp', help="report path (left or base)") 
    parser.add_argument('rpt_fp2', nargs='?', help="report path (right for compare)") 
    parser.add_argument('-c', dest='cfg_fp', metavar='<config>', 
                                help="configuration file") 
    return parser


def main():
    """Main Function"""
    parser = create_argparse()
    args = parser.parse_args()
    default_cfg = ".pt_ana_cons.setup"

    if args.cfg_fp is None and os.path.exists(default_cfg):
        if os.path.isfile(default_cfg):
            args.cfg_fp = default_cfg

    rpt_fps = ([args.rpt_fp] if args.rpt_fp2 is None 
                else [args.rpt_fp, args.rpt_fp2])
    report_cons_summary(rpt_fps, args.cfg_fp)


if __name__ == '__main__':
    main()


