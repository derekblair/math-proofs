function compositions(q, max) {
  if (q===0) return [[]];
  return Array.from({length: Math.min(q,max)},(_,i)=>i+1)
    .flatMap(s=>compositions(q-s,max).map(p=>[s,...p]));
}
function invariant(q, max, steps) {
  let total=0;
  const visited=new Set([0]);
  for(const step of steps){total+=step;visited.add(total%q);}
  if(total!==q)throw Error("wrong winding");
  let tested=0;
  for(let start=0;start<q;start++) for(let edges=0;edges<=q;edges++){
    let holds=true;
    for(const vertex of visited)if((vertex-start+q)%q>edges){holds=false;break;}
    if(holds){
      if(edges<q-max)throw Error("bad path length");
      tested++;
    }
  }
  return tested;
}
let compositionsTested=0, connectedCovers=0, subdivisions=0;
for(let q=2;q<=12;q++) for(let d=1;d<q;d++){
  for(const steps of compositions(q,d)){
    connectedCovers+=invariant(q,d,steps);
    compositionsTested++;
  }
  const k=Math.ceil(q/d);
  const steps=Array(k).fill(d);
  steps[k-1]=q-(k-1)*d;
  if(steps.some(s=>s<1||s>d)||steps.reduce((a,b)=>a+b)!==q)throw Error("subdivision split");
  subdivisions++;
}
console.log(JSON.stringify({compositionsTested,connectedCovers,subdivisions}));