# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ldt_move as lm, json
G=2**64-2**32+1
P256=2**256-2**224+2**192+2**96-1
tabs={'T1 GF128 (3187,455)':(3187,455,2**128,132),'T2 Fq^6 (3187,455)':(3187,455,8380417**6,132),
'T3 P256 (3187,455)':(3187,455,P256,132),'T4 hash1 (3230,461)':(3230,461,2**128,132),
'T5 Fq^9 (6746,963)':(6746,963,12289**9,134),'T7 Fp128 (6916,988)':(6916,988,2**128-2**108+1,132),
'T8 GF128 (1883,269)':(1883,269,2**128,132),'T9 GF128 (4081,583)':(4081,583,2**128,132),
'T6 Gold2 (28672,4096)':(28672,4096,G**2,135)}
which=sys.argv[1:] or list(tabs)
for name in tabs:
    if not any(w in name for w in which): continue
    N,k,F,t=tabs[name]
    b=lm.best(N,k,t,F,'untested','b',subfield=False)
    tm=lm.t_min(N,k,F,'untested','b',108,subfield=False)
    print(json.dumps(dict(tab=name,t=t,bits_at_t=round(b[0],3),A=b[1],rounds={kk:round(v,2) for kk,v in b[2].items()},tmin108=tm)),flush=True)
