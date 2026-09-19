from fractions import Fraction as F
import random
def G(V,N,bW,a,I,M):
    q=F(M,I); return (F(V)*N/I + bW)/(a + q*N)
random.seed(2); best=None
for _ in range(40000):
    I=2**random.choice([16,18,20]); M=random.randint(I//64,I//8); q=F(M,I)
    N=random.randint(I//2,I)          # real regime: N >= 2^127 = I/2
    a=random.randint(0,int(q*N)); bW=random.randint(0,a); V=random.randint(a,min(M,a+int(q*I)))
    x=G(V,N,bW,a,I,M); pv=q; phit=F(V,I); pnew=pv-phit; h=(F(a-bW,V) if V else F(0))
    e=(1-pv)*G(V,N-1,bW,a,I,M)+pnew*G(V+1,N-1,bW,a+1,I,M)+phit*(h*G(V,N-1,bW+2,a+1,I,M)+(1-h)*G(V,N-1,bW+1,a+1,I,M))
    c=(e-x)*I
    if best is None or c>best[0]: best=(c,I,M,N,a,bW,V)
print("worst own-message charge / eps:", float(best[0]), best[1:])
