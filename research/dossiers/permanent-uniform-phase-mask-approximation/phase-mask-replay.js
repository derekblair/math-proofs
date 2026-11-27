'use strict';
const abs=x=>x<0n?-x:x;
const gcd=(a,b)=>b===0n?abs(a):gcd(b,a%b);
const z=(a,b,d)=>{const g=gcd(gcd(a,b),d);return [a/g,b/g,d/g];};
const norm=(a,b)=>z(a*a-b*b,2n*a*b,a*a+b*b);
const conj=(a)=>[a[0],-a[1],a[2]];
const mul=([a,b,d],[c,e,f])=>z(a*c-b*e,a*e+b*c,d*f);
let seed=42;const rng=m=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>12)%m;};
let count=0,blocks=0,examined=0;
for(let n=3;n<=45;n++)for(let run=0;run<35;run++){
 const S=Array.from({length:n},()=>Array.from({length:n},()=>norm(BigInt(1+rng(31)),BigInt(rng(61)-30))));
 const cols=Array.from({length:n},(_,j)=>j);
 for(let i=0;cols.length>=3;i+=2){
   const a=cols.slice(0,3),p=a.map(j=>mul(S[i][j],conj(S[i+1][j])));
   let best;
   for(let j=0;j<3;j++)for(let k=j+1;k<3;k++){
      const ph=mul(p[j],conj(p[k]));examined++;
      if(2n*abs(ph[0])>=ph[2])best=[a[j],a[k],ph];
   }
   if(!best)throw Error("three phase angle cover");
   const [j,k,ph]=best;
   const ratioNumerator=2n*ph[2]+2n*abs(ph[0]);
   if(2n*ratioNumerator<6n*ph[2] || ratioNumerator>4n*ph[2])throw Error("2x2 local determinant ratio");
   cols.splice(cols.indexOf(j),1);cols.splice(cols.indexOf(k),1);blocks++;
 }
 if(n-cols.length!==2*Math.floor((n-1)/2))throw Error("block count");
 count++;
}
console.log(JSON.stringify({masks:count,blocks,examined}));