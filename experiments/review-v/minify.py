import re,sys
def minify(src):
    out=[];i=0;n=len(src);prev=''
    def isword(c): return c.isalnum() or c=='_'
    while i<n:
        c=src[i]
        if c=='/' and i+1<n and src[i+1]=='/':
            while i<n and src[i]!='\n': i+=1
            continue
        if c=='"':
            j=i+1
            while j<n and src[j]!='"':
                if src[j]=='\\': j+=1
                j+=1
            out.append(src[i:j+1]); prev='"'; i=j+1; continue
        if c.isspace():
            # keep one space only if between two word chars
            j=i
            while j<n and src[j].isspace(): j+=1
            if j<n and out and isword(out[-1][-1]) and isword(src[j]): out.append(' ')
            i=j; continue
        out.append(c); i+=1
    return ''.join(out)
for n in sys.argv[1:]:
    src=open(f"c/tests/{n}.wl").read()
    m=minify(src)
    open(f"{sys.argv[0].rsplit('/',1)[0]}/wl/{n}.wl","w").write(m)
    print(n,len(src),"->",len(m))
