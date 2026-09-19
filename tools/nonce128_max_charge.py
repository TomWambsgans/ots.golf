import random
# float model, index space I, valid set M, q = M/I, eps = 1/I
def G(r,q,N,a,bW):
    return (r*q*N + bW)/(a + q*N)
def charge(I,M,msgs,VW,m0):
    q=M/I; eps=1/I
    V=sum(a-b for (a,b,N) in msgs)+VW; r=V/M
    Gs=[G(r,q,N,a,b) for (a,b,N) in msgs]+[r]   # last: untouched message
    mx=max(Gs)
    # m0: index into msgs, or -1 for a fresh untouched message (N=I, a=b=0)
    base=list(msgs)+[(0,0,I)]
    k0=m0 if m0>=0 else len(msgs)
    def mx_after(r2, own, extra):   # own: new (a,b,N) of m0 ; extra: dict m -> +bW
        best=r2
        for i,(a,b,N) in enumerate(base):
            if i==k0: a,b,N=own
            b+=extra.get(i,0)
            best=max(best,G(r2,q,N,a,b))
        return best
    a0,b0,N0=base[k0]
    E=0.0
    pv=q; phit=V/I; pnew=pv-phit
    E+=(1-pv)*mx_after(r,(a0,b0,N0-1),{})
    E+=pnew*mx_after(r+1/M,(a0+1,b0,N0-1),{})
    # hits on non-W entry of each message i (prob (a-b)/I each)
    for i,(a,b,N) in enumerate(base):
        if a-b>0:
            p=(a-b)/I
            if i==k0: E+=p*mx_after(r,(a0+1,b0+2,N0-1),{})
            else: E+=p*mx_after(r,(a0+1,b0+1,N0-1),{i:1})
    E+=(VW/I)*mx_after(r,(a0+1,b0+1,N0-1),{})
    return (E-mx)/eps
random.seed(3); worst=(0,None)
I=2**24; M=2**11
for trial in range(3000):
    kind=random.choice(['singles','pairs','mixed','big'])
    msgs=[]
    budget=int(M*random.uniform(0.05,0.95))   # total valid entries ~ |V|
    while budget>0:
        if kind=='singles': a=1;b=0
        elif kind=='pairs': a=2;b=random.choice([0,1])
        elif kind=='big': a=random.randint(1,budget);b=random.randint(0,a)
        else: a=random.randint(1,5);b=random.randint(0,a)
        a=min(a,budget); b=min(b,a); budget-=a
        N=I-random.randint(int(a*I/M*0.5),int(a*I/M*2)+1)
        N=max(N,I//2)
        msgs.append((a,b,N))
    VW=sum(b for (_,b,_) in msgs)//2
    if len(msgs)>400: msgs=msgs[:400]; VW=sum(b for (_,b,_) in msgs)//2
    for m0 in [-1]+random.sample(range(len(msgs)),min(3,len(msgs))):
        c=charge(I,M,msgs,VW,m0)
        if c>worst[0]: worst=(c,kind,len(msgs),m0)
print("worst max-potential charge / eps:",worst)
