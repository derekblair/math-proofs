
function simpson(f,a,b,n) {
  const h=(b-a)/n;
  let result=f(a)+f(b);
  for(let i=1;i<n;i++)result+=(i%2?4:2)*f(a+i*h);
  return result*h/3;
}
function saddle(A,r){
  if(!r)return 0;
  return 4*r/(A+Math.sqrt(A*A+32*r*r));
}
function cOverRootD(d){
  // Gamma quotient sqrt(d)^(-1) times c_d. Recurrence + exact low-dimensional starts.
  let c=d%2?0.5:1/Math.PI;
  for(let j=d%2?3:2;j<d;j+=2)c*=j/(j-1);
  return c/Math.sqrt(d);
}
function angular(d,A,r,g0) {
  const t=saddle(A,r), alpha=A+2*r*t;
  const sg=alpha*Math.sqrt(1-t*t);
  const lo=Math.max(-12,(-1-t)*Math.sqrt(d)),hi=Math.min(12,(1-t)*Math.sqrt(d));
  const val=simpson(u=>{
    const z=t+u/Math.sqrt(d), at=A+2*r*z, g=at*Math.sqrt(Math.max(0,1-z*z));
    if(g<=0||at<=0)return 0;
    return (at/sg)**3 * Math.exp((d-3)*Math.log(g/sg));
  },lo,hi,240);
  return cOverRootD(d)*val*Math.exp(d*Math.log(sg/g0));
}
function optimum(alpha){
  const p=1/alpha;
  const derivative = l=>simpson(u=>p*u**(p-1)*Math.exp(-l*u)*(1-l*u),0,1,2000);
  let lo=0,hi=8;
  for(let j=0;j<55;j++){
    const m=(lo+hi)/2;
    if(derivative(m)>0)lo=m;else hi=m;
  }
  return (lo+hi)/2;
}
function diagnose(d,ell){
  const eps=1/(d*Math.log(d)),A=ell+eps,R=(1-eps)/2;
  const t=saddle(A,R),g=(A+2*R*t)*Math.sqrt(1-t*t);
  const t0=saddle(ell,0.5), g0=(ell+t0)*Math.sqrt(1-t0*t0);
  const alpha=t0/(ell+t0), p=1/alpha, lambda=optimum(alpha);
  const Z=1/Math.sqrt((1-t0*t0)*(1+2*t0*t0));
  const rawC=lambda/Z*simpson(s=>p*s**(p-1)*Math.exp(-lambda*s),0,1,2000);
  const radialEnd=angular(d,A,R,g);
  const radial=simpson(s=>{
    if(!s)return 0;
    const x=s**p,r=R*x**(1/d);
    return p*s**(p-1)*Math.exp(-lambda*angular(d,A,r,g)/radialEnd);
  },0,1,480);
  const finiteGeometry=lambda*radial/radialEnd;
  return {ell,d,lambda,c:rawC,beta:2*g0,angularPrefactor:radialEnd,limitZ:Z,finiteGeometry,
    scaledDensity:finiteGeometry*Math.exp(d*Math.log(R*2*g0/g)),
    halfUnionRelativeErrorBound:0.5*lambda*Math.exp(d*Math.log(A/g))/radialEnd};
}
for(const ell of [1,1.1,1.5,2,5]){
 for(const d of [16,64,256,1024,4096,16384])console.log(JSON.stringify(diagnose(d,ell)));
}
