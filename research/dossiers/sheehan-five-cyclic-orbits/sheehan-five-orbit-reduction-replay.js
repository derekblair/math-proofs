const red=["01","12","23","34","04"],types=[[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]],V=[0,1,2,3,4];
function P(a){return a.length?a.flatMap(v=>P(a.filter(x=>x!==v)).map(q=>[v,...q])):[[]]}
const e=(a,b)=>[a,b].sort().join(""),m=x=>(x+20)%5;
function orbit(F){return V.flatMap(k=>[1,-1].map(s=>F.map(([a,b])=>e(m(k+s*a),m(k+s*b))).sort().join(","))).sort()[0]}
const fs=new Set;
for(const T of types)for(const p of P(V)){let F=[],j=0;for(const n of T){for(let t=0;t<n;t++)F.push([p[j+t],p[j+(t+1)%n]]);j+=n;}fs.add(orbit(F));}
const H=P([1,2,3,4]).filter(p=>p[0]<p[3]).map(p=>[0,...p]).map(p=>p.map((u,i)=>e(u,p[(i+1)%5])));
function ok(b){if(!b)throw Error("certificate failed");}ok(fs.size===17);
let bad=[],counts={};
for(const z of [...fs].sort()){
 const F=z.split(","),E=red.concat(F),loop=v=>F.includes(e(v,v));
 const adjacent=V.some(v=>loop(v)&&loop(m(v+1)));
 const parallel=F.filter(s=>red.includes(s)).length>=2;
 const other=H.some(Q=>Q.every(s=>E.includes(s))&&Q.some(s=>!red.includes(s))&&Q.some(s=>E.filter(x=>x===s).length>=2));
 const complete=new Set(E).size===10&&E.every(x=>x[0]!==x[1]);
 const tag=adjacent?"adjacent rims":parallel?"2 red-parallel choices":other?"alternate with parallel choice":complete?"K5 identity":"residual";
 counts[tag]=(counts[tag]||0)+1;
 if(tag==="residual")bad.push(z);
}
ok(bad.join("|")==="00,12,14,24,33");
let q=["01243","01324","01342","01423","01432","02134"],a=[-3,5,-1,3,-3,-4];
const edgeVec=w=>{let out={};for(let i=0;i<5;i++){let x=w[i],y=w[(i+1)%5];out[e(x,y)]=x<y?1:-1;}return out}
let w=edgeVec("01234");
for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)ok(q.reduce((s,t,k)=>s+a[k]*(edgeVec(t)[e(i,j)]||0),0)===(w[e(i,j)]||0));
console.log(counts,"residual",bad);
