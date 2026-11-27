'use strict';
// Literal 16/16/16 theta charts for three bridge-3 digons in series.
const charts=[{"p":9,"s":1,"D":3,"f":{"L":16,"arms":[[9,8,17,26,30,39,48,41,32,19,28],[9,0,10,1,11,2,12,3,13,4,14,5,15,24,28],[9,18,31,40,49,42,51,44,53,37,28]]}},{"p":9,"s":-1,"D":3,"f":{"L":16,"arms":[[9,0,10,19,35,26,33,24,15,5,14,4,13],[9,8,17,7,16,25,32,23,30,21,12,3,13],[9,18,27,36,49,40,31,22,13]]}},{"p":27,"s":1,"D":3,"f":{"L":16,"arms":[[27,0,28,1,29,56,83,73,100,63,36,8,35],[27,26,53,25,52,24,51,78,88,61,34,7,35],[27,54,81,108,135,116,89,62,35]]}},{"p":27,"s":-1,"D":3,"f":{"L":16,"arms":[[27,0,28,1,29,2,30,3,31,4,32,5,33,6,34,7,35],[27,26,53,25,52,24,51,78,97,70,89,62,35],[27,54,100,73,92,65,38,10,37,9,36,8,35]]}}];
function check({p,s,D,f:{L,arms}}){
 const mod=x=>(x%p+p)%p, used=new Set, ends=[arms[0][0],arms[0].at(-1)], edges=new Set;
 if(D!==3||L!==16||arms.length!==3)throw Error('shape');
 for(const arm of arms){
  if(arm[0]!==ends[0]||arm.at(-1)!==ends[1]||new Set(arm).size!==arm.length||ends[0]===ends[1])throw Error('endpoints');
  let w=0;
  for(let i=0;i+1<arm.length;i++){
   const [u,v]=[arm[i],arm[i+1]].sort((a,b)=>a-b), a=Math.floor(u/p), b=Math.floor(v/p), h=mod(v-u), e=u+':'+v;
   if(a<0||b>=2*D||b!==a+1||edges.has(e))throw Error('edge');
   edges.add(e);
   if(a%2){if(h)throw Error('bridge shift');w+=3;}
   else {if(h&&h!==mod(1+s*(a/2)*p/3))throw Error('digon shift');w++;}
  }
  if(w!==L)throw Error('weight');
  for(const v of arm.slice(1,-1)){if(used.has(v))throw Error('overlap');used.add(v);}
 }
}
for(const c of charts)check(c);
console.log(charts.length+' literal equal theta charts verified');
