from fractions import Fraction as Q
from itertools import product
# Both lattice basis vectors have length L, with angle acos(c).
L,c,s=Q(8,5),Q(20,101),Q(99,101)
ct,st=Q(9999,10001),Q(200,10001)
assert c*c+s*s == ct*ct+st*st == 1
C2,S2=ct*ct-st*st,2*ct*st
cy,sy=c*C2+s*S2,s*C2-c*S2 # angle after inward rotation by 2 theta
assert 0<c<cy<1 and 0<sy<s and cy*cy+sy*sy == 1
R,A=Q(1,2),Q(1)
h,hy=(L-A)/2,(L*ct-A)/2
assert L<2 and 2*L*L*(1-c)>4 and 4*L*L*(1-c)>4
# Any coefficients with |m|>=2 or |n|>=2 exceed length 2 by the eigenvalue bound.
for m,n in product(range(-1,2),repeat=2):
    if abs(m)+abs(n)==2:
        assert L*L*(m*m+n*n+2*c*m*n)>4
for (z,u) in [(c,h),(cy,hy)]:
    # Largest corner squared radius for equally wide acute slabs.
    assert 2*u*u/(1-z)<R*R
rad_area=4*h*h/s
tilt_area=4*hy*hy/sy
assert tilt_area>rad_area
print("exact radial and tilted areas:",rad_area,tilt_area)
print("area improvement:",float(tilt_area/rad_area-1))

# Individual origin-to-offset segment safety does not imply joint safety.
a,b,l=Q(1,20),Q(2,5),Q(11,10)
assert a*a+b*b<R*R
assert l*l*b*b/(a*a+b*b)>1 # distance to line <= distance to segment
assert l-2*a==1
print("verified finite-lattice tilt and pointwise-versus-joint counterexamples")
