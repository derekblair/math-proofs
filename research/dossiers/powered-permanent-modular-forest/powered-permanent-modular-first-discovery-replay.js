'use strict';
let seed = 0x93e13213;
const pick = n => {seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed % n;};
let trials=0, falseIdentifications=0, charges=0, sharp=0;
for(let t=0;t<12000;t++){
  const n=8+pick(39), k=1+pick(5), q=Array.from({length:k},()=>2+pick(4));
  const par=[-1], color=[-1], phi=[Array(k).fill(0)];
  for(let v=1;v<n;v++){
    const p=pick(v), c=pick(k+1)-1;
    par.push(p); color.push(c);
    const dv=phi[p].slice();
    if(c>=0)dv[c]=(dv[c]+(pick(2)===0?1:q[c]-1))%q[c];
    phi.push(dv);
  }
  const bad=q.map((m,c)=>new Set(phi.map(p=>p[c])).size===m&&pick(4)!==0);
  const z=phi[0], belongs=v=>phi[v].every((x,c)=>!bad[c]||x===z[c]);
  const root=[0], sizes=Array(n).fill(0), fiber=Array(n).fill(0), count=Array(n).fill(0);
  let F=0, Sbad=0;
  for(let v=1;v<n;v++){
    const c=color[v], inF=c<0||bad[c];
    root.push(inF?root[par[v]]:v);
    if(inF)F++;
  }
  for(let v=0;v<n;v++){sizes[root[v]]++;if(belongs(v))fiber[root[v]]++;}
  const D=fiber.reduce((s,f)=>s+Math.max(0,f-1),0);
  for(let c=0;c<k;c++)if(bad[c]){
    const seen=new Set([z[c]]);
    for(let v=1;v<n;v++)if(!seen.has(phi[v][c])){
      if(color[v]!==c||belongs(v))throw Error('bad first discovery');
      seen.add(phi[v][c]); count[root[v]]++; charges++;
    }
    if(seen.size!==q[c])throw Error('coverage');
    Sbad+=q[c]-1;
  }
  for(let v=0;v<n;v++)if(sizes[v]&&count[v]>sizes[v]-fiber[v]-(fiber[v]===0?1:0))
    throw Error('component charge');
  if(D>F-Sbad)throw Error('global charge');
  if(D===F-Sbad)sharp++;
  trials++;falseIdentifications+=D;
}
console.log(JSON.stringify({trials,identifications:falseIdentifications,charges,sharp}));
