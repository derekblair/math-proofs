function classify(l){
  const m=3*l-1;
  const mod=x=>(x%m+m)%m;
  function test(kind,delta,overlap=false){
    const h=Array(m).fill(0), L=Array(m).fill(0), Q=Array(m).fill(0);
    function pulse(type,s){
      if(type==="L"){L[mod(s+l-1)]=1;for(let j=0;j<l-1;j++)h[mod(s+j)]++;}
      else {Q[s]=1;for(let j=0;j<l;j++)h[mod(s+j)]++;}
    }
    pulse(kind[0],0);pulse(kind[1],delta);
    const G=Array.from({length:2*m},()=>[]);
    function add(z,s){const i=mod(3*z),j=m+mod(i+s);G[i].push(j);G[j].push(i);}
    for(let i=0;i<m;i++){
      if(h[i]>1)throw Error("double H");
      const P=h[i]+L[i]-Q[i];if(P<0||P>1)throw Error("bad P");
      if(!h[i])add(i,3);if(!L[i])add(i,2);if(P)add(i,0);if(Q[i])add(i,1);
    }
    if(G.some(x=>x.length!==2))throw Error("bad deg");
    const seen=Array(2*m).fill(false);const lens=[];
    for(let i=0;i<2*m;i++)if(!seen[i]){
      const bfs=[i];seen[i]=true;
      for(let j=0;j<bfs.length;j++)for(const x of G[bfs[j]])if(!seen[x]){seen[x]=true;bfs.push(x);}
      lens.push(bfs.length);
    }
    return lens.sort((a,b)=>a-b).join("/");
  }
  const out={l};
  for(const kind of ["LL","QQ","LQ"]){
    const start=kind==="LQ"?l-1:l;
    out[kind]=Array.from({length:2*l-start},(_,i)=>test(kind,i+start));
  }
  return out;
}
let reps=0, quadraticCertificates=0;
for(let l=2;l<=110;l++){
  const m=3*l-1, c=classify(l), N=String(2*m);
  if(c.LL.length!==l||c.QQ.length!==l||c.LQ.length!==l+1)throw Error("count");
  c.LL.forEach((x,j)=>{if((x!==N)!==(j===0||j===l-1))throw Error("component classification");});
  if([...c.QQ,...c.LQ].some(x=>x!==N))throw Error("Q case");
  reps+=c.LL.length+c.QQ.length+c.LQ.length;quadraticCertificates++;
}
function literal(l){
  const m=3*l-1,k=2*l;
  const shifts=[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]];
  let factors=0, hams=0;
  const degree=Array(m).fill(0), assignments=[];
  function rec(i,blue,deficit){
    if(i===m){
      if(blue!==k||deficit!==2)return;
      factors++;
      const G=Array.from({length:2*m},()=>[]);
      assignments.forEach((s,r)=>s.forEach(q=>{
        const v=m+(r+q)%m;G[r].push(v);G[v].push(r);
      }));
      const seen=new Set([0]),todo=[0];
      for(let p=0;p<todo.length;p++)for(const v of G[todo[p]])if(!seen.has(v)){seen.add(v);todo.push(v);}
      if(todo.length===2*m)hams++;
      return;
    }
    for(const ss of shifts){
      const nextB=blue+ss.filter(x=>x<2).length;
      const nextD=deficit+Number(!ss.includes(2))+Number(ss.includes(1));
      if(nextB>k||nextD>2||nextB+2*(m-i-1)<k)continue;
      const cols=ss.map(x=>(i+x)%m);
      if(cols.some(c=>degree[c]===2))continue;
      cols.forEach(c=>++degree[c]);assignments.push(ss);
      rec(i+1,nextB,nextD);
      assignments.pop();cols.forEach(c=>--degree[c]);
    }
  }
  rec(0,0,0);
  if(factors!==m*(2*l+1)||hams!==2*m*l)throw Error(JSON.stringify([l,factors,hams]));
  return [m,factors,hams];
}
const literalSizes=[];for(let l=2;l<=7;l++)literalSizes.push(literal(l));
console.log({reps,quadraticCertificates,literalSizes});
