#include <array>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using Mat=std::array<std::array<int,9>,9>;
int p;
Mat one() { Mat m={}; for(int i=0;i<9;i++)m[i][i]=1; return m; }
Mat mul(Mat a,Mat b) {
 Mat m=one();
 for(int i=0;i<9;i++)for(int j=i+1;j<9;j++){
   int v=0;for(int k=i;k<=j;k++)v+=a[i][k]*b[k][j];
   m[i][j]=v%p;
 }
 return m;
}
Mat inv(Mat m) {Mat r=one(); for(int i=0;i<p-1;i++)r=mul(r,m); assert(mul(m,r)==one()); return r;}
Mat elem(std::array<int,8> t) {
  Mat r=one();for(int i=0;i<8;i++)r[i][i+1]=t[i]; return r;
}
Mat rim[2][2];
const int Back[3]={1,0,2};
struct Vert { int b; Mat m; };

Vert step(Vert v,int port){if(port==2)return {1-v.b,v.m};return {v.b,mul(v.m,rim[v.b][port])};}
bool equals(const Vert& v,const Vert& w){return v.b==w.b && v.m==w.m;}
bool word(std::string s,int r=0) {
 Vert v={r,one()}; std::vector<Vert> seen{v};
 for(int i=0;i<int(s.size());++i){
  v=step(v,s[i]-'0');
  if(i==int(s.size())-1)return equals(v,seen[0]);
  if(std::any_of(seen.begin(),seen.end(),[&](const Vert& t){return equals(v,t);}))return false;
  seen.push_back(v);
 }
 return false;
}

int main(){
 p=17;
 int cases=0;
 for(int a=0;a<p;a++) for(int b=0;b<p;b++){
 rim[0][0]=elem({4,4,4,10,7,1,1,a});rim[0][1]=inv(rim[0][0]);
 rim[1][0]=elem({12,12,9,12,2,0,1,b});rim[1][1]=inv(rim[1][0]);
 Mat t=rim[1][0];
 for(int k=0;k<7;++k)t=mul(mul(mul(t,rim[0][0]),inv(t)),rim[0][1]);
 if(t[0][8]==0)continue;
 if(!word("20202112112020020212121212002021202021211212002002121202121120202020212112120020021212121200202120202112112020020212120212112020"))continue;
 if(cases++==0)std::cout<<"Positive C128, pair of exact class eight: appended "<<a<<" "<<b<<", eighth commutator "<<t[0][8]<<"\n";
 }
 std::cout<<cases<<" exact witness parameter pairs\n";
 return cases==0?1:0;
}
