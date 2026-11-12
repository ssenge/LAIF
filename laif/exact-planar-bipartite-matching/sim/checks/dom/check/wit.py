# Witnesses for line 41 and line 89 of the note, from the definitions only.
def reach(arcs, src, allow):
    seen=set(s for s in src if s in allow); st=list(seen)
    while st:
        u=st.pop()
        for v in arcs.get(u,()):
            if v in allow and v not in seen: seen.add(v); st.append(v)
    return seen
def tables(k, extra):
    arcs={}
    for i in range(1,k): arcs.setdefault(i,set()).add(i+1)
    for u,v in extra: arcs.setdefault(u,set()).add(v)
    V=set(arcs)|{v for vs in arcs.values() for v in vs}
    R=list(range(1,k+1)); O=V-set(R)
    feed={i:reach(arcs,arcs.get(i,()),O) for i in R}; feed[0]=set()
    out={}
    for t in range(2,k+1):
        js=[i for i in range(0,k+1) if i not in (t,t-1) and ((i>=1 and t in arcs.get(i,())) or any(t in arcs.get(u,()) for u in feed[i]))]
        out[t]=(min(js,default='inf'),max(js,default='-inf'))
    ab={y:(min(i for i in feed if y in feed[i]),max(i for i in feed if y in feed[i])) for y in O}
    return out[3],ab
print('with p5>u:',tables(7,[(2,'u'),(5,'u'),(7,'u'),('u',3)]))
print('without  :',tables(7,[(2,'u'),(7,'u'),('u',3)]))
