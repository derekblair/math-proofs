"""Uniform h=6 and h=8 parameter certificates for both selected-entry rates."""
from check_depth_baseline import F,H,box_rate,l2,log,point,plus,times,minus,divide

def certify(h,c,t,delta,alpha,revised):
    c,t,delta,alpha=map(F,(c,t,delta,alpha))
    q=divide(plus(H(t),times(point(t),log(4))),l2)
    g=box_rate(c,t) if revised else divide(times(point(t),log((c-1)/4)),l2)
    R=divide(l2,plus(minus(minus(times(point(c),log(5)),times(point(c/2),H(1/c))),
                         times(point(c-1),l2)),times(g,l2)))
    p=h+delta
    margins=[minus(times(point(p),g),point(2*delta)),
             minus(point(1-delta),times(point(p),q)),minus(R,point(alpha*p))]
    assert min(m[0] for m in margins)>0
    print(h,revised,'margin lower bounds',*[f'{float(m[0]):.12g}' for m in margins],
          'exact saving',alpha*delta,'raw exponent',float(2-alpha*delta))

if __name__=='__main__':
    certify(8,'11.42','.01177','.06555','.009071',False)
    certify(8,'11.35','.01177','.06553','.009130',True)
    certify(6,'11.30','.01641','.06792','.012186',False)
    certify(6,'11.21','.01641','.06793','.012288',True)
