const roots=[[1,0],[0,1],[-1,0],[0,-1]];
const add=([a,b],[c,d])=>[a+c,b+d];
const mul=([a,b],[c,d])=>[a*c-b*d,a*d+b*c];
const conj=([a,b])=>[a,-b];
const norm=([a,b])=>a*a+b*b;
let seed=80979983;
function next(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>16)%4;}
function gadget(m,u,v){
  const rest=Array.from({length:m},(_,i)=>i).filter(i=>i!==u&&i!==v);
  return [[...new Set([u,v])],[...new Set([u,v])],...rest.slice(0,m-2).map(j=>[j])];
}
function expansion(pattern,mask){
  let determinant=[0,0], permanent=0;
  const assignment=[];
  function visit(used,sign,prod){
    if(assignment.length===pattern.length){
      determinant=add(determinant,prod.map(x=>x*sign));
      permanent++;
      return;
    }
    const i=assignment.length;
    for(const j of pattern[i]){
      if(used&(1<<j))continue;
      const inverse=assignment.filter(x=>x>j).length;
      assignment.push(j);
      visit(used|(1<<j),inverse%2?-sign:sign,mul(prod,mask[i][j]));
      assignment.pop();
    }
  }
  visit(0,1,[1,0]);
  return [permanent,norm(determinant)];
}
let gadgetChecks=0, HouseholderChecks=0, tensorEntries=0;
for(let m=2;m<=12;m++){
  for(let i=0;i<m;i++)for(let j=0;j<m;j++){
    let product=0;
    for(let l=0;l<m;l++)product+=(2-m*Number(i===l))*(2-m*Number(l===j));
    if(product!==m*m*Number(i===j))throw Error("reflection square");
    ++HouseholderChecks;
  }
  for(let sample=0;sample<50;sample++){
    const mask=Array.from({length:m},()=>Array.from({length:m},()=>roots[next()]));
    const ratios=mask[0].map((x,j)=>mul(x,conj(mask[1][j])));
    for(let u=0;u<m;u++)for(let v=0;v<m;v++){
      const [p,d]=expansion(gadget(m,u,v),mask);
      const expected=2-2*mul(ratios[u],conj(ratios[v]))[0];
      if(p!==(u===v?0:2)||d!==expected)throw Error("gadget identity");
      ++gadgetChecks;
    }
  }
  for(let k=1;k<=3;k++){
    if(m**(2*k)>1e6)continue;
    let support=0, scaledDualPairing=0;
    for(let i=0;i<m**k;i++)for(let j=0;j<m**k;j++){
      let p=i,q=j, justSupport=true, witness=1;
      for(let t=0;t<k;t++){
        const equal=p%m===q%m;
        justSupport&&=!equal;
        witness*=2-m*Number(equal);
        p=Math.floor(p/m);q=Math.floor(q/m);
      }
      if(justSupport){support++;scaledDualPairing+=witness;}
      tensorEntries++;
    }
    if(support!==(m*(m-1))**k || scaledDualPairing!==m**k*(2*(m-1))**k)throw Error("tensor pairing");
  }
}
console.log({gadgetChecks,HouseholderChecks,tensorEntries});
