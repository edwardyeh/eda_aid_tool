#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# SPDX-License-Identifier: GPL-2.0-only
#
# PrimeTime Report Analysis
#
# Copyright (C) 2023 Yeh, Hsin-Hsien <yhh76227@gmail.com>
#
import argparse
import csv
import gzip
import os
import re

import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt

from decimal import Decimal, ROUND_HALF_UP

from .utils.common import PKG_VERSION, PT_TS_VER
from .utils.primetime_ts import Pin, TimePath, TimeReport

VERSION = f"pt_ana_ts version {PT_TS_VER} ({PKG_VERSION})"


##############################################################################
### Function


class Palette:
    bar_default = "#caccd1"
    bar = (
        "#84bd00", "#efdf00", "#fe5000", "#e4002b", 
        "#da1884", "#a51890", "#0077c8", "#008eaa", 
        "#74d2e7", "#48a9c5", "#0085ad", "#8db9ca", 
        "#4298b5", "#005670", "#004182", "#44712e",
        "#915907", "#b24020", "#dce6f1", "#d7ebce",
        "#fce2ba", "#fadfd8", "#0a66c2", "#83941f",
        "#e7a33e", "#f5987e",
    )


def load_times_cfg(cfg_fp) -> dict:
    """Load configuration."""
    attr = {
        'clock_check_enable':                       ('ckc_en'           , False),
        'delta_sum_enable':                         ('dts_en'           , False),
        'path_segment_enable':                      ('seg_en'           , False),
        'ckm_with_non_clock_cell':                  ('ckm_nock'         , False),
        'through_pin_on_report':                    ('thp_on_rpt'       , False),
        'slack_on_report':                          ('slk_on_rpt'       , True),
        'clock_uncertainty_on_report':              ('unce_on_rpt'      , False),
        'library_required_on_report':               ('lib_on_rpt'       , False),
        'datapath_level_on_report':                 ('dplv_on_rpt'      , False),
        'clock_skew_on_report':                     ('ck_skew_on_rpt'   , True),
        'segment_data_latency_on_report':           ('seg_dlat_on_rpt'  , True),
        "segment_data_delta_on_report":             ('seg_ddt_on_rpt'   , True),
        'segment_launch_clk_latency_on_report':     ('seg_llat_on_rpt'  , True),
        'segment_launch_clk_delta_on_report':       ('seg_ldt_on_rpt'   , True),
        'segment_capture_clk_latency_on_report':    ('seg_clat_on_rpt'  , True),
        'segment_capture_clk_delta_on_report':      ('seg_cdt_on_rpt'   , True),
        'segment_capture_clk_latency_include_crpr': ('seg_clat_inc_crpr', True),
    }

    cons_cfg = dict(attr.values())
    cons_cfg.update({
        'bds': {}, 'ckpc': set(), 'ckpi': set(), 'ckpr': [],
        'hcd': {},  # format: {cell: {'pi:po': tag, ...}, ...}
        'ckt': [], 'ckm': [], 'dpc': None, 'pc': {}, 'cc': {}, 'dc': {},
    })

    if cfg_fp is None:
        return cons_cfg

    with open(cfg_fp, 'r') as fp:
        for fno, line in enumerate(fp, 1):
            line = line.split('#')[0].strip()
            if line:
                try:
                    key, value = line.split(':')
                    key, value = key.strip(), value.strip()
                    if key in attr:
                        change_value = str(not attr[key][1]).lower()
                        if value.lower() == change_value:
                            cons_cfg[attr[key][0]] = not attr[key][1]
                        else:
                            cons_cfg[attr[key][0]] = attr[key][1]
                    elif key == 'bds':
                        tag, *pat = value.split()
                        cons_cfg['bds'][tag] = pat
                    elif key == 'ckt':
                        tag, pat = value.split()
                        pat_re = re.compile(pat)
                        match tag.lower():
                            case 'y': tag = True
                            case 'n': tag = False
                            case  _ : raise SyntaxError
                        cons_cfg['ckt'].append((tag, pat_re))
                    elif key == 'ckp':
                        type_, *pat = value.split()
                        match type_:
                            case 'c': cons_cfg['ckpc'].update(pat)
                            case 'i': cons_cfg['ckpi'].update(pat)
                            case 'r': cons_cfg['ckpr'].extend(
                                        [re.compile(i) for i in pat])
                            case  _ : raise SyntaxError
                    elif key == 'ckm':
                        pat = re.compile(value.split()[0])
                        cons_cfg['ckm'].append(pat)
                    elif key == 'dpc':
                        cons_cfg['dpc'] = value
                    elif key == 'pc':
                        tag, pat = value.split()
                        cons_cfg['pc'][tag] = re.compile(pat)
                    elif key == 'cc':
                        tag, pat = value.split()
                        cons_cfg['cc'][tag] = re.compile(pat)
                    elif key == 'dc':
                        v1, v2, *_ = value.split()
                        if v1 == 'r':
                            cons_cfg['dc']['re'] = re.compile(v2)
                        else:
                            cons_cfg['dc'][v2] = Decimal(v1)
                    elif key == 'hcd':
                        toks = value.split('"') 
                        if len(toks) > 1:
                            type_, pi, po, tag = *toks[0].split(), toks[1]
                        else:
                            type_, pi, po, tag = toks[0].split()
                        hcd_dict = cons_cfg['hcd'].setdefault(type_, {})
                        cons_cfg['hcd'][type_][f"{pi}:{po}"] = tag
                except Exception:
                    raise SyntaxError(f"config syntax error (ln:{fno})")

    if cons_cfg['dpc'] is not None and cons_cfg['dpc'] not in cons_cfg['pc']:
        print(" [INFO] Specific group for default path isn't existed," + 
                " ignore.\n")
        cons_cfg['dpc'] = None

    return cons_cfg


def report_summary(args, range_list: list):
    """Report the timing summary of paths."""
    cons_cfg = load_times_cfg(args.cfg_fp)
    time_rpt = TimeReport(
                cell_ckp=cons_cfg['ckpc'],
                inst_ckp=cons_cfg['ckpi'],
                ickp_re=cons_cfg['ckpr'],
                hcd=cons_cfg['hcd'],
                ckt=cons_cfg['ckt'],
                ckm=cons_cfg['ckm'],
                ckm_nock=cons_cfg['ckm_nock'],
                dpc=cons_cfg['dpc'],
                pc=cons_cfg['pc'],
                cc=cons_cfg['cc'],
                dc=cons_cfg['dc'])

    time_rpt.parse_report(args.rpt_fp, range_list)

    if args.is_debug:
        print("\n=== Option:")
        print(time_rpt.opt)
        for no, path in enumerate(time_rpt.path, 1):
            print(f"\n=== Path {no}:")
            msg = path.__repr__()
            for line in msg.split(','):
                print(line)
        return

    csv_row, csv_table = {}, []
    if args.csv_fp is not None:
        if args.csv_ctype is not None:
            csv_head = ['ln'] + args.csv_ctype
        else:
            csv_head = ['ln', 'arr', 'req', 'slk']
        if 'slat' in csv_head:
            csv_head = (csv_head[:(idx:=csv_head.index('slat'))] 
                        + ['sllat', 'sclat', 'bllat', 'bclat'] 
                        + csv_head[idx+1:])
        csv_row = dict([(s, None) for s in csv_head])
        csv_table.append([s.upper() for s in csv_head])

    for pid, path in enumerate(time_rpt.path):
        # import pdb; pdb.set_trace()
        splen = len(stp:=path.lpath[path.spin].name)
        if (plen:=len(edp:=path.lpath[-1].name)) < splen:
            plen = splen

        ## path information
        print(" {}".format("=" * 60))
        if path.max_dly_en:
            print(" Startpoint: {}".format(stp))
            print(" Endpoint:   {}".format(edp))
        elif plen > 80:
            print(" Startpoint: {}".format(stp))
            print("             ({} {})".format(path.sed, path.sck))
            print(" Endpoint:   {}".format(edp))
            print("             ({} {})".format(path.eed, path.eck))
        else:
            print(" Startpoint: {} ({} {})".format(stp.ljust(plen), 
                                                   path.sed, path.sck))
            print(" Endpoint:   {} ({} {})".format(edp.ljust(plen), 
                                                   path.eed, path.eck))
        print(" Path group: {}".format(path.group))
        print(" Delay type: {}".format(path.type))
        if path.scen is not None:
            print(" Scenario:   {}".format(path.scen))
        if cons_cfg['thp_on_rpt'] and path.thp:
            print(" {}".format("-" * 60))
            for thp in path.thp:
                print(" Through:    {}".format(thp))
        print(" {}".format("=" * 60))

        ## path latency
        dlat = path.arr - path.idly - path.llat - path.sev
        if cons_cfg['slk_on_rpt']:
            print(" {:26}{: 5.4f}".format( "data latency:", dlat))
            print(" {:26}{: 5.4f}".format("arrival:", path.arr))
            print(" {:26}{: 5.4f}".format("required:", path.req))
            print(" {:26}{: 5.4f}".format("slack:", path.slk))
            if (path.idly_en or path.odly_en or path.pmarg_en or path.hcd or 
                cons_cfg['unce_on_rpt'] or cons_cfg['lib_on_rpt']):
                print(" {}".format("-" * 60))
            if cons_cfg['unce_on_rpt']:
                print(" {:26}{: 5.4f}".format(
                    "clock uncertainty:", path.unce))
            if cons_cfg['lib_on_rpt'] and not path.odly_en:
                print(" {:26}{: 5.4f}".format(
                    ("library setup:" if path.type == "max" 
                    else "library hold"), path.lib))
            if path.idly_en:
                print(" {:26}{: 5.4f}".format("input delay:", path.idly))
            if path.odly_en:
                print(" {:26}{: 5.4f}".format("output delay:", -1*path.odly))
            if path.pmarg_en:
                print(" {:26}{: 5.4f}".format("path margin:", path.pmarg))
            for tag, val in path.hcd.items():
                print(" {}{: 5.4f}".format(f"{tag}:".ljust(26), val))
            if cons_cfg['dplv_on_rpt']:
                print(" {:26}{: 5.4f}".format(
                    "datapath level:", len(path.lpath)-path.spin-1))

            print(" {}".format("=" * 60))

        ## clock latency & check
        is_clk_on_rpt = False
        skew = path.llat - path.clat - path.crpr

        if cons_cfg['ck_skew_on_rpt']:
            is_clk_on_rpt = True
            if not path.max_dly_en:
                print(" {:26}{: 5.4f}".format("launch clock edge value:", path.sev))
                print(" {:26}{: 5.4f}".format("capture clock edge value:", path.eev))
            print(" {:26}{: 5.4f}".format("launch clock latency:", path.llat))
            if not path.max_dly_en:
                print(" {:26}{: 5.4f}".format("capture clock latency:", path.clat))
                print(" {:26}{: 5.4f}".format("crpr:", path.crpr))
                print(" {:26}{: 5.4f}".format("clock skew:", skew))

        if (args.ckc_en or cons_cfg['ckc_en']) and not path.max_dly_en:
            if is_clk_on_rpt:
                print(" {}".format("-" * 60))
            is_clk_on_rpt = True

            gcc_rslt, scc_rslt, ctc_rslt = time_rpt.clock_path_check(
                                            pid=pid, is_dump=args.ckc_dump)

            spath_len = ((path.spin+1) if path.sgpi is None 
                         else (path.spin-path.sgpi))
            epath_len = (len(path.cpath) if path.egpi is None 
                         else (len(path.cpath)-path.egpi-1))
            
            col_sz = len(split_lv:=f"{spath_len}/{epath_len}/{scc_rslt[0]}")
            print(" {:26} {}    {}".format("clock cell type check:", 
                                            ctc_rslt[0].ljust(col_sz), 
                                            ctc_rslt[1]))
            print(" {:26} {}    {}".format("clock source path match:", 
                                            gcc_rslt[0].ljust(col_sz), 
                                            gcc_rslt[1]))
            print(" {:26} {}    (ln:{}:{})".format("clock network path fork:", 
                                            split_lv, *scc_rslt[1:]))

        if path.max_dly_en:
            is_clk_on_rpt = True
            print(" {:26}{: 5.4f}".format("max delay:", path.max_dly))
        if is_clk_on_rpt or path.max_dly_en:
            print(" {}".format("=" * 60))

        ## clock & path delta
        if args.dts_en or cons_cfg['dts_en']:
            if 'delta' in time_rpt.opt:
                ddt_val = "{: 5.4f}".format(path.ddt)
                if not {'pfc', 'pfce'}.isdisjoint(time_rpt.opt):
                    ldt_val = "{:5.4f}".format(path.ldt)
                    cdt_val = "{:5.4f}".format(path.cdt)
                else:
                    ldt_val, cdt_val = 'N/A', 'N/A'
            else:
                ddt_val, ldt_val, cdt_val = 'N/A', 'N/A', 'N/A'

            print(" {:26}{} : {} : {}".format("total delta (D:L:C):", 
                                              ddt_val, ldt_val, cdt_val))
            print(" {}".format("=" * 60))

        ## path segment
        if (args.seg_en or cons_cfg['seg_en']) and not len(cons_cfg['pc']):
            print(" Segment: path classify patterns is unexisted.")
            print(" {}".format("=" * 60))
        elif (args.seg_en or cons_cfg['seg_en']) and len(cons_cfg['pc']):
            seg_dict = time_rpt.get_path_segment(pid)

            if 'pf' in time_rpt.opt:
                is_dseg_pass, is_ckseg_pass = False, True
                print(" Segment:  (report path type: full)")
            elif 'pfc' in time_rpt.opt:
                is_dseg_pass, is_ckseg_pass = False, False
                print(" Segment:  (report path type: full_clock)")
            elif 'pfce' in time_rpt.opt:
                is_dseg_pass, is_ckseg_pass = False, False
                print(" Segment:  (report path type: full_clock_expanded)")
            else:
                is_dseg_pass, is_ckseg_pass = True, True
                print(" Segment:  (report path type: unknown)")

            # data latency & delta
            if not is_dseg_pass:
                if cons_cfg['seg_dlat_on_rpt'] or cons_cfg['seg_ddt_on_rpt']:
                    print(" {}".format("-" * 60))
                if cons_cfg['seg_dlat_on_rpt']:
                    print(" data latency: ", end='')
                    for tag, val in seg_dict['dlat']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    print()
                if cons_cfg['seg_ddt_on_rpt']:
                    print(" data delta:   ", end='')
                    for tag, val in seg_dict['ddt']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    print()

            if not is_ckseg_pass:
                # launch clock latency & delta
                if cons_cfg['seg_llat_on_rpt'] or cons_cfg['seg_ldt_on_rpt']:
                    print(" {}".format("-" * 60))
                if cons_cfg['seg_llat_on_rpt']:
                    print(" launch clk latency:  ", end='')
                    print("SC:{: .4f} ".format(path.sllat), end='')
                    for tag, val in seg_dict['llat']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    print()
                if cons_cfg['seg_ldt_on_rpt']:
                    print(" launch clk delta:    ", end='')
                    for tag, val in seg_dict['ldt']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    print()

                # capture clock latency & delta
                if cons_cfg['seg_clat_on_rpt'] or cons_cfg['seg_cdt_on_rpt']:
                    print(" {}".format("-" * 60))
                if cons_cfg['seg_clat_on_rpt']:
                    print(" capture clk latency: ", end='')
                    if cons_cfg['seg_clat_inc_crpr']:
                        sclat = path.sclat + path.crpr
                    else:
                        sclat = path.sclat
                    print("SC:{: .4f} ".format(sclat), end='')
                    for tag, val in seg_dict['clat']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    if cons_cfg['seg_clat_inc_crpr']:
                        print(" (include crpr)")
                    else:
                        print()
                if cons_cfg['seg_cdt_on_rpt']:
                    print(" capture clk delta:   ", end='')
                    for tag, val in seg_dict['cdt']:
                        print("{}:{: .4f} ".format(tag, val), end='')
                    print()

            print(" {}".format("=" * 60))
        elif args.csv_fp is not None and 'slat' in args.csv_ctype:
            seg_dict = time_rpt.get_path_segment(pid)

        print()

        ## create csv
        if args.csv_fp is not None:
            for key in csv_row.keys():
                if key == 'stp':
                    csv_row[key] = stp
                elif key == 'edp':
                    csv_row[key] = edp
                elif key == 'dlat':
                    csv_row[key] = dlat
                elif key == 'sclat' and cons_cfg['seg_clat_inc_crpr']:
                    csv_row[key] = path.sclat + path.crpr
                elif key == 'bllat':
                    csv_row[key] = path.llat - path.sllat
                elif key == 'bclat':
                    csv_row[key] = path.clat - path.sclat
                elif key == 'skew':
                    csv_row[key] = skew
                else:
                    csv_row[key] = path.__dict__[key]
            csv_table.append(list(csv_row.values()))

    ## export csv
    if args.csv_fp is not None:
        with open(args.csv_fp, 'w', newline='') as csvf:
            spamw = csv.writer(csvf, delimiter=' ')
            for row in csv_table:
                spamw.writerow(row)

    ## show time bar chart
    bar_dtype = set()  # data type of bar charts
    if args.bar_set is not None:
        if len(cons_cfg['bds']) and args.bar_set in cons_cfg['bds']:
            bar_dtype |= set(cons_cfg['bds'][args.bar_set])
        else:
            print(" [WARNING] The -bars option cannot find" +
                  " in the configuration, ignore.\n")
    if args.bar_dtype is not None:
        bar_dtype |= (set(args.bar_dtype) if args.bar_dtype 
                      else set(['p','c','t','d','i','ct']))
    if 'ct' in bar_dtype:
        bar_dtype.add('i')

    if len(bar_dtype) != 0:
        if args.bar_ptype is None or len(args.bar_ptype) == 0:
            bar_ptype = set(['f', 'd'])  # path type of bar charts
        else:
            bar_ptype = set(args.bar_ptype)
            if 'f' in bar_ptype:
                bar_ptype.add('d')

        show_time_bar(time_rpt.path[-1], time_rpt.opt, cons_cfg, 
                      bar_dtype, bar_ptype, args.bar_rev)


def show_time_bar(path: TimePath, path_opt: set, cons_cfg: dict, 
                  bar_dtype: set, bar_ptype: set, is_rev: bool):
    """
    Show the time path on the barchart.

    Arguments
    ---------
    path      : path data.
    path_opt  : report options.
    cons_cfg  : configurations.
    bar_dtype : data type of a barchart.
    bar_ptype : path type of a barchart.
    is_rev    : axis reverse.
    """
    db, db_dict = [], {}

    dtype_list = [
        ['c', 'cap', "Cap (pf)"],         # [c]apacitance
        ['p', 'phy', "Distance (um)"],    # [p]hysical distance
        ['t', 'tran', "Tran (ns)"],       # [t]ransition
        ['d', 'delta', "Delta (ns)"],     # [d]elta
        ['i', 'incr', "Increment (ns)"],  # latency [i]ncrement
    ]

    for key, tag, title in dtype_list:
        if key in bar_dtype and tag in path_opt:
            db_dict[key], data = [], []

            # create launch-clock/data path list
            for cid, cell in enumerate(path.lpath):
                data.append(cell.__dict__[tag])
                if cid == path.spin:
                    if 'l' in bar_ptype:
                        db_dict[key].append(
                            [f"Launch Clk {title}", data.copy()])
                    if 'd' not in bar_ptype:
                        data = None
                        break
                    if 'f' not in bar_ptype:
                        data = [data[-1]]
            ddata = data

            # create capture clock path list
            if 'c' in bar_ptype:
                data = []
                for cell in path.cpath:
                        data.append(cell.__dict__[tag])
                db_dict[key].append([f"Capture Clk {title}", data])

            # add data path list after capture clock path list
            if ddata is not None:
                db_dict[key].append([f"Path {title}", ddata])
        else:
            bar_dtype.discard(key)
            
    is_ct = 'ct' in bar_dtype
    is_cc = is_ct and len(cons_cfg['cc']) > 0
    is_dc = is_ct and len(cons_cfg['dc']) > 0

    if is_dc:
        db_dict['dc'], data = [], []

        # create launch-clock/data path list
        for cid, cell in enumerate(path.lpath):
            data.append(cell.drv)
            if cell.drv < 0:
                print("WARNING: Unknown driving cell. ({}, ln:{})".format(
                        cell.cell, cell.ln))
            if cid == path.spin:
                if 'l' in bar_ptype:
                    db_dict['dc'].append([f"Launch Cell Type", data.copy()])
                if 'd' not in bar_ptype:
                    data = None
                    break
                if 'f' not in bar_ptype:
                    data = [data[-1]]
        ddata = data

        # create capture clock path list
        if 'c' in bar_ptype:
            data = []
            for cell in path.cpath:
                data.append(cell.drv)
                if cell.drv < 0:
                    print("WARNING: Unknown driving cell. ({}, ln:{})".format(
                            cell.cell, cell.ln))
            db_dict['dc'].append([f"Capture Cell Type", data])

        # add data path list after capture clock path list
        if ddata is not None:
            db_dict['dc'].append([f"Path Cell Type", ddata])

    # reorder database
    if 'p' in db_dict:          # physical distance
        db.extend(db_dict['p'])
    if 'c' in db_dict:          # capacitance
        c_plist = db_dict['c']
        for key, plist in db_dict.items():
            if key != 'c':
                for i, clist in enumerate(plist):
                    if len(c_plist[i]) < len(clist):
                        c_plist[i].insert(0, 0.0)
                break
        db.extend(c_plist)
    if 't' in db_dict:          # transition
        db.extend(db_dict['t'])
    if 'd' in db_dict:          # delta
        db.extend(db_dict['d'])
    if 'i' in db_dict:          # latency increment
        db.extend(db_dict['i'])
    if 'dc' in db_dict:         # driving
        db.extend(db_dict['dc'])

    if len(db):
        default_tag = 'TP' if cons_cfg['dpc'] is None else cons_cfg['dpc']

        ce_info = get_time_bar_info('name', default_tag, cons_cfg['pc'], 
                                    bar_ptype, path)

        if is_ct:
            ct_info = get_time_bar_info('cell', 'UN', cons_cfg['cc'], 
                                        bar_ptype, path)
        elif not is_dc:
            bar_dtype.discard('ct')

        bar_ptype.discard('f')
        dtype_cnt, ptype_cnt = len(bar_dtype), len(bar_ptype)

        if is_rev:
            cy_cnt, cx_cnt = ptype_cnt, dtype_cnt
        else:
            cy_cnt, cx_cnt = dtype_cnt, ptype_cnt

        fig, axs = plt.subplots(cy_cnt, cx_cnt, constrained_layout=True)
        # import pdb; pdb.set_trace()

        pt_anno_list = [[] for i in range(dtype_cnt*ptype_cnt)]
        bbox = dict(boxstyle='round', fc='#ffcc00', alpha=0.6)
        arrow = dict(arrowstyle='->', connectionstyle="arc3,rad=0.")

        ct_type_cnt = (dtype_cnt-1) if is_ct else None

        for y in range(dtype_cnt):
            if (is_ct_proc:=(y == ct_type_cnt)):
                bar_info = ct_info
                dtype_off = ptype_cnt * (y if is_dc else (y-1))
            else:
                bar_info = ce_info
                dtype_off = ptype_cnt * y

            for x in range(ptype_cnt):
                sdb = db[dtype_off+x]
                aid = (cx_cnt*x+y) if is_rev else (cx_cnt*y+x)
                labels = list(bar_info['lg'][x].keys())
                handles = [plt.Rectangle((0,0), 1, 1, color=bar_info['lg'][x][label]) 
                           for label in labels]
                level = range(0, len(sdb[1]))

                max_dy = max(sdb[1])
                min_dy = 0 if (min_dy:=min(sdb[1])) > 0 else min_dy
                dy_off = 4 if (is_ct_proc and not is_dc) else (max_dy-min_dy)
                dx, dy_rt = -0.5, 0.5
                dy = min_dy + dy_off * dy_rt

                xlist = [*level]

                # move the startpoint clock pin to the last of xlist to 
                # make sure the highlight pattern is on the top layer.
                if bar_info['did'] is not None and bar_info['did'] == x:
                    xlist.append(xlist[bar_info['dsp']])
                    del xlist[bar_info['dsp']]

                axs = plt.subplot(cy_cnt, cx_cnt, aid+1)

                for ix in xlist:
                    toks = bar_info['ce'][x][ix].name.split('/')
                    name = (f".../{toks[-2]}/{toks[-1]}" if len(toks) > 2 
                           else bar_info['ce'][x][ix].name)
                    if is_ct_proc:
                        val = f"lib: {bar_info['ce'][x][ix].cell}"
                        iy = -(max(sdb[1])/4.0) if is_dc else 1.0
                    else:
                        val = "val: {:.4f}".format(iy:=sdb[1][ix])

                    comm = "pin: {}\n{}\nln: {}".format(
                                name, val, bar_info['ce'][x][ix].ln)
                    pt, = axs.bar(ix, iy, width=1.0, 
                                  color=bar_info['c'][x][ix], 
                                  hatch=bar_info['ha'][x][ix], 
                                  ec=bar_info['ec'][x][ix])
                    anno = plt.annotate(comm, xy=(ix,iy), xytext=(dx,dy), 
                                        bbox=bbox, arrowprops=arrow, size=10)
                    anno.set_visible(False)
                    info = {'dx': dx, 'min_dy': min_dy, 
                            'dy_off': dy_off, 'dy_rt': dy_rt, 
                            'ce': bar_info['ce'][x][ix], 'plv': 2, 
                            'ct': is_ct_proc}
                    pt_anno_list[aid].append([pt, anno, info])

                if is_ct_proc:
                    axs.set_title(sdb[0].split()[0] + " Cell Type")
                    if is_dc:
                        ix2 = sorted(xlist)
                        iy2 = [sdb[1][i] for i in ix2]
                        axs.stem(ix2, iy2, 'o-')
                        # axs.plot(ix2, iy2, 'o-', lw=1)
                        dy = (my:=max(sdb[1])) / 4.0
                        axs.set_ylim(-dy, my+dy*1.5)
                    else:
                        axs.set_ylim(0, 4)
                else:
                    axs.set_title(sdb[0])
                    dy = (my:=max(sdb[1])) / 4.0  
                    axs.set_ylim(min(sdb[1]), my+dy)

                axs.grid(axis='y', which='both', ls=':', c='grey')
                axs.set_xticks(level, [])
                axs.legend(handles, labels, loc='upper left', ncol=len(labels))

        # def on_move(event):
        #     is_vis_chg = False
        #     for i in range(len(pt_anno_list)):
        #         for pt, anno, _ in pt_anno_list[i]:
        #             is_vis = (pt.contains(event)[0] == True)
        #             if is_vis != anno.get_visible():
        #                 is_vis_chg = True
        #                 anno.set_visible(is_vis)
        #     if is_vis_chg:
        #         plt.draw()

        def on_mouse(event):
            ev_key = str(event.button)
            # print(ev_key)
            if ev_key in {'MouseButton.LEFT', '1'}:
                for i in range(len(pt_anno_list)):
                    is_act, vis_list = False, []
                    for pt, *_ in pt_anno_list[i]:
                        vis_list.append(pt.contains(event)[0] == True)
                        is_act = is_act or vis_list[-1]
                    if is_act:
                        for is_vis, pt_anno in zip(vis_list, pt_anno_list[i]):
                            if is_vis != pt_anno[1].get_visible():
                                pt_anno[1].set_visible(is_vis)
            elif ev_key in {'MouseButton.RIGHT', '3'}:
                for i in range(len(pt_anno_list)):
                    for pt, anno, _ in pt_anno_list[i]:
                        anno.set_visible(False)
            plt.draw()

        def on_key(event):
            ev_key, val = key_event_check(str(event.key))
            # print(str(event.key))
            match ev_key:
                case 'ESC':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, _ in pt_anno_list[i]:
                            anno.set_visible(False)
                    plt.draw()
                case 'UD':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, info in pt_anno_list[i]:
                            info['dy_rt'] += val 
                            anno.set_y(info['min_dy']
                                       + info['dy_off']*info['dy_rt'])
                    plt.draw()
                case 'LR':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, info in pt_anno_list[i]:
                            anno.set_x(anno._x+val)
                    plt.draw()
                case 'PM':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, info in pt_anno_list[i]:
                            info['plv'] = (plv:=info['plv']+val)
                            toks = (name:=info['ce'].name).split('/')
                            if len(toks) > plv:
                                name = ""
                                for i in range(-1, -1-plv, -1):
                                    name = "/{}".format(toks[i]) + name 
                                name = '...' +name 
                            toks = anno.get_text().split('\n')
                            anno.set_text(
                                    f"pin: {name}\n{toks[-2]}\n{toks[-1]}")
                    plt.draw()
                case 'BT':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, info in pt_anno_list[i]:
                            toks = anno.get_text().split('\n')
                            if val == 2 and info['ct'] is False:
                                toks[0] = "{}\nlib: {}".format(
                                            toks[0], info['ce'].cell)
                            anno.set_text(f"{toks[0]}\n{toks[-2]}\n{toks[-1]}")
                    plt.draw()
                case 'RESET':
                    for i in range(len(pt_anno_list)):
                        for pt, anno, info in pt_anno_list[i]:
                            if anno._x == -0.5 and info['dy_rt'] == 0.5:
                                info['plv'] = 2
                                toks = (name:=info['ce'].name).split('/')
                                if len(toks) > 2:
                                    name = f'.../{toks[-2]}/{toks[-1]}'
                                toks = anno.get_text().split('\n')
                                anno.set_text(
                                        f"pin: {name}\n{toks[-2]}\n{toks[-1]}")
                            info['dy_rt'] = 0.5
                            anno.set_x(-0.5)
                            anno.set_y(info['min_dy']
                                       + info['dy_off']*info['dy_rt'])
                    plt.draw()

        # fig.canvas.mpl_connect('motion_notify_event', on_move)
        fig.canvas.mpl_connect('button_press_event', on_mouse)
        fig.canvas.mpl_connect('key_press_event', on_key)
        plt.show()


def get_time_bar_info(aid: str, default_tag: str, seg_dict: dict, 
                      bar_ptype: set, path: TimePath):
    """
    Get the time bar information.

    Arguments
    ---------
    aid         : cell attribute for path segment.
    default_tag : default legend tag.
    seg_dict    : segment configuration.
    bar_ptype   : path types of the bar chart.
    path        : path data.

    Returns
    -------
    bar_info : the information of the barchart. (dict) 
    """
    pal_cnt = len(Palette.bar)
    bar_palette = {}

    if not len(seg_dict):
        default_color = Palette.bar_default if aid == 'cell' else Palette.bar[0]
        init_tag = None
    else:
        default_color = Palette.bar_default 
        init_tag = default_tag if default_tag in seg_dict else None
        for i, key in enumerate(seg_dict.keys()):
            bar_palette[key] = Palette.bar[i%pal_cnt]

    bar_info = {
        'ce': [],     # cell objects of each bar 
        'c':  [],     # color of each bar
        'ha': [],     # hatch pattern of each bar
        'ec': [],     # edge color of each bar
        'lg': [],     # legend list
        'did': None,  # list index of data path
        'dsp': None,  # index of the startpoint clock pin in data path list 
    }

    for type_ in ('l', 'c', 'd'):
        if type_ in bar_ptype:
            tag, pal_idx = init_tag, -1
            lv_ce_path, lv_c_path = [], []
            lv_ha_path, lv_ec_path = [], []

            if init_tag is None:
                bar_lg_path = {default_tag: default_color}
            else:
                bar_lg_path = {}

            s_path = path.cpath if type_ == 'c' else path.lpath

            for cid, cell in enumerate(s_path):
                # check path classification tag
                if not len(seg_dict):
                    pass
                elif (tag is None 
                        or seg_dict[tag].fullmatch(cell.__dict__[aid]) is None):
                    new_tag = init_tag 
                    for key, ps_re in seg_dict.items():
                        if (m:=ps_re.fullmatch(cell.__dict__[aid])):
                            new_tag = key
                            break
                    tag = new_tag

                # reset if path type is data only
                if cid == path.spin and type_ == 'd' and 'f' not in bar_ptype:
                    pal_idx = -1
                    if init_tag is None:
                        bar_lg_path = {default_tag: default_color}
                    else:
                        bar_lg_path = {}
                    lv_ce_path, lv_c_path = [], []
                    lv_ha_path, lv_ec_path = [], []

                # add tag to bar legend
                key = default_tag if tag is None else tag
                if key not in bar_lg_path:
                    bar_lg_path[key] = bar_palette[key]

                # add bar setting for cell
                lv_ce_path.append(cell)
                lv_c_path.append(bar_lg_path[key])
                if cid == path.spin and type_ == 'd':
                    bar_info['did'] = len(bar_info['ha'])
                    bar_info['dsp'] = len(lv_ha_path)
                    lv_ha_path.append('/')
                    lv_ec_path.append('b')
                else:
                    lv_ha_path.append('')
                    lv_ec_path.append('k')

            if len(seg_dict):
                m_bar_lg_path = {default_tag: default_color}
                for key in seg_dict.keys():
                    if key in bar_lg_path:
                        m_bar_lg_path[key] = bar_lg_path[key]
            else:
                m_bar_lg_path = bar_lg_path

            bar_info['lg'].append(m_bar_lg_path)
            bar_info['ce'].append(lv_ce_path)
            bar_info['c'].append(lv_c_path)
            bar_info['ha'].append(lv_ha_path)
            bar_info['ec'].append(lv_ec_path)

    return bar_info


def key_event_check(action):
    """Check Key Event"""
    if action == 'escape': return 'ESC'  ,  0    # remove all comment bubble
    if action == 'up':     return 'UD'   ,  0.1  # up shift bubble
    if action == 'down':   return 'UD'   , -0.1  # down shift bubble
    if action == 'left':   return 'LR'   , -0.5  # left shift bubble
    if action == 'right':  return 'LR'   ,  0.5  # right shift bubble
    if action == 'a':      return 'PM'   ,  1    # increase pin hierarchical
    if action == 'd':      return 'PM'   , -1    # decrease pin hierarchical
    if action == '1':      return 'BT'   ,  1    # bubble type 1 (pin, val, ln)
    if action == '2':      return 'BT'   ,  2    # bubble type 2 (pin, lib, val, ln)
    if action == 'r':      return 'RESET',  0    # reset bubble
    return "NONE", 0


##############################################################################
### Main


def create_argparse() -> argparse.ArgumentParser:
    """Create Argument Parser"""
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawTextHelpFormatter,
        description="PrimeTime Report Analysis\n" + 
                    "  -- Timing Path Summary\n" +
                    "  -- command: report_timing")

    parser.add_argument('rpt_fp', help="report_path") 
    parser.add_argument('-version', action='version', version=VERSION)
    parser.add_argument('-debug', dest='is_debug', action='store_true', 
                            help="enable debug mode")
    parser.add_argument('-c', dest='cfg_fp', metavar='<config>', 
                            help="set the config file path") 
    parser.add_argument('-nc', dest='is_nocfg', action='store_true', 
                            help="disable to load the config file\n ")
    parser.add_argument('-r', dest='range', metavar='<value>', 
                            help="report scan range select,\n" + 
                                 "ex: 6,16+2,26:100,26:100+2\n" +
                                 "(default load 1 path from line 0)\n ") 
    parser.add_argument('-ckc', dest='ckc_en', action='store_true', 
                            help="enable clock path check")
    parser.add_argument('-ckcd', dest='ckc_dump', action='store_true', 
                            help="dump clock path check contents to the file")
    parser.add_argument('-dts', dest='dts_en', action='store_true', 
                            help="enable clock/data path delta summation")
    parser.add_argument('-seg', dest='seg_en', action='store_true', 
                            help="enable path segment\n ")
    parser.add_argument('-bard', dest='bar_dtype', metavar='<pat>', nargs='*', 
                            choices=['p','c','t','d','i', 'ct'],
                            help="bar view data type select (default: all)\n" +
                                 "p: distance, c: cap, t: tran, d: delta, i: incr, ct: cell_type\n ") 
    parser.add_argument('-barp', dest='bar_ptype', metavar='<pat>', nargs='*', 
                            choices=['f','d','l','c'],
                            help="bar view path type select (default: full_data)\n" +
                                 "f: full_data, d: data, l: launch_clk, c: capture_clk\n ") 
    parser.add_argument('-bars', dest='bar_set', metavar='<tag>', 
                            help="bar view data type set defined in the config file") 
    parser.add_argument('-barr', dest='bar_rev', action='store_true', 
                            help="axis reverse for bar view\n ")
    parser.add_argument('-csv', dest='csv_fp', metavar='<path>', 
                            help="export CSV file") 
    parser.add_argument('-csvc', dest='csv_ctype', metavar='<pat>', nargs='*', 
                            choices=['stp', 'edp', 
                                     'dlat', 'arr', 'req', 'slk', 'unce', 'lib', 
                                     'llat', 'clat', 'slat', 'crpr', 'skew',
                                     'ddt', 'ldt', 'cdt'],
                            help="CSV column type:\n" +
                                 "  stp  - startpoint\n" +
                                 "  edp  - endpoint\n" +
                                 "  dlat - data latency\n" +
                                 "  arr  - arrival time\n" +
                                 "  req  - required time\n" +
                                 "  slk  - slack\n" +
                                 "  unce - clock uncertainty\n" +
                                 "  lib  - library setup/hold time\n" +
                                 "  llat - launch clock latency\n" +
                                 "  clat - capture clock latency\n" +
                                 "  slat - clock source latency\n" +
                                 "  crpr - CRPR\n" +
                                 "  skew - clock skew\n" +
                                 "  ddt  - data delta\n" +
                                 "  ldt  - launch clock delta\n" +
                                 "  cdt  - capture clock delta\n" ) 
    return parser


def main():
    """Main Function"""
    parser = create_argparse()
    args = parser.parse_args()
    default_cfg = ".pt_ana_ts.setup"

    if args.is_nocfg:
        args.cfg_fp = None
    elif args.cfg_fp is None and os.path.exists(default_cfg):
        if os.path.isfile(default_cfg):
            args.cfg_fp = default_cfg

    range_list = []
    if args.range is not None:
        range_re = re.compile(r"(?P<st>\d+)(?::(?P<ed>\d+))?(?:\+(?P<nu>\d+))?")
        for range_ in args.range.split(','):
            if (m:=range_re.fullmatch(range_)):
                st = int(m.group('st'))
                ed = None if (ed:=m.group('ed')) is None else int(ed)
                nu = None if (nu:=m.group('nu')) is None else int(nu)
                range_list.append([st, ed, nu])
    if not range_list:
        range_list.append([0, None, 1])  # [start_line, last_line, path_count]
    
    print("\n Report: {}\n".format(os.path.abspath(args.rpt_fp)))
    report_summary(args, range_list)


if __name__ == '__main__':
    main()


