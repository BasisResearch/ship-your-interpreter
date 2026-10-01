#!/usr/bin/env python3
"""Round-4 census: declaration units of VsaIris/Interp by conclusion head, binder shape and tactic mix.
Usage: census.py <repo> [modtimes-log]"""
import re, sys, os, json, collections, subprocess

repo = sys.argv[1]
root = os.path.join(repo, 'VsaIris/Interp')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure|#ix_piece|#ix_seg|#ix_branch|#derive_case)\b\s*([^\s:({\[]*)')
END = re.compile(r'^(end\b|section\b|namespace\b|open\b|variable\b|/--|/-!|--|set_option|attribute|macro|syntax|elab|@\[|theorem|lemma|def|abbrev|instance|structure|#ix_piece|#ix_seg|#ix_branch|#derive_case|private|protected|noncomputable|scoped|local|notation|infix)')
TACS = ['iframe','ihave','iintro','iapply','isplitl','isplitr','isplit','icases','iexact','ipureintro','iexists','imodintro','iexfalso','irevert','ispecialize','iassumption','ileft','iright','inext','iloeb',
        'omega','sym_run','nx_run','sx_run','refine','simp','simp only','ix_reg','ix_fwd','rw','exact','decide','obtain','have','unfold','ArmAt.','ms_call','callFrame','iperm']

def units(path):
    L = open(path).read().split('\n')
    i = 0; out = []
    while i < len(L):
        m = DECL.match(L[i])
        if m:
            j = i + 1
            while j < len(L) and not (L[j] and not L[j][0].isspace() and END.match(L[j])):
                j += 1
            # strip trailing blank lines
            k = j
            while k > i and L[k-1].strip() == '': k -= 1
            out.append((m.group(1), m.group(2), i + 1, L[i:k]))
            i = j
        else:
            i += 1
    return out

def split_stmt(lines):
    txt = '\n'.join(lines)
    d = 0
    for i, ch in enumerate(txt):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and txt.startswith(':=', i): return txt[:i], txt[i:]
        elif d == 0 and txt.startswith(' by', i) and (i + 3 == len(txt) or txt[i+3] in ' \n'):
            return txt[:i], txt[i:]
    return txt, ''

def concl(s):
    d=0; last_t=-1; last_c=-1
    for i,ch in enumerate(s):
        if ch in '([{⟨': d+=1
        elif ch in ')]}⟩': d-=1
        elif d==0 and ch=='⊢': last_t=i
        elif d==0 and ch==':' and (i+1<len(s) and s[i+1] not in '=') and (i==0 or s[i-1]!=':'): last_c=i
    if last_t>=0: return s[last_t+1:]
    if last_c>=0: return s[last_c+1:]
    return s

def head(stmt, kind, name):
    s = stmt
    if kind in ('def', 'abbrev', 'structure', 'instance'):
        if kind == 'structure': return 'structure'
        if re.search(r':\s*Prop\s*$', s.strip()): return 'def:Prop'
        if re.search(r':\s*IProp', s): return 'def:IProp'
        return 'def:other'
    c = concl(s).strip()
    if re.search(r'\.W\s+Φ|\bWP\b|twp|wpW', c): return 'WP'
    toks = re.findall(r"[A-Za-z_][A-Za-z_0-9.']*", c)
    if not toks: return 'unknown'
    t = toks[0]
    return t

rows = []
for dp, _, fs in os.walk(root):
    for f in sorted(fs):
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, repo)
        for kind, name, ln, lines in units(p):
            stmt, body = split_stmt(lines)
            h = head(stmt, kind, name)
            binder = []
            if re.search(r'\(Wp : MachWP', stmt): binder.append('Wp')
            if 'hlc : HasLC' in stmt or 'HasLC' in stmt: binder.append('HasLC')
            if re.search(r'⊢', stmt): binder.append('entails')
            tc = {t: len(re.findall(r'(?<![A-Za-z_])' + re.escape(t) + (r'(?![A-Za-z_])' if not t.endswith('.') else ''), body)) for t in TACS}
            irisT = sum(tc[t] for t in TACS[:20])
            rows.append(dict(file=rel, kind=kind, name=name, line=ln, lines=len([x for x in lines if x.strip()]),
                             stmt_lines=len([x for x in stmt.split('\n') if x.strip()]), head=h, binder=binder, tacs=tc, iris=irisT))

json.dump(rows, open(os.path.join(os.path.dirname(__file__), 'units.json'), 'w'))
by = collections.defaultdict(lambda: [0, 0, set(), 0])
for r in rows:
    b = by[r['head']]; b[0] += 1; b[1] += r['lines']; b[2].add(r['file']); b[3] += r['iris']
print('%-28s %6s %7s %5s %7s' % ('head', 'units', 'lines', 'files', 'irisTac'))
for h, (n, l, fs, it) in sorted(by.items(), key=lambda x: -x[1][1])[:40]:
    print('%-28s %6d %7d %5d %7d' % (h, n, l, len(fs), it))
tot = collections.Counter()
for r in rows:
    for t, c in r['tacs'].items(): tot[t] += c
print('tactic totals:', tot.most_common())
print('units', len(rows), 'lines', sum(r['lines'] for r in rows))
