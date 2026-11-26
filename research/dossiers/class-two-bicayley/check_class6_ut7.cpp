#include <array>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>
using Mat=std::array<std::array<int,7>,7>;
int p;
Mat one() { Mat m={}; for(int i=0;i<7;i++)m[i][i]=1; return m; }
Mat mul(Mat a,Mat b) {
 Mat m=one();
 for(int i=0;i<7;i++)for(int j=i+1;j<7;j++){
   int v=0;for(int k=i;k<=j;k++)v+=a[i][k]*b[k][j];
   m[i][j]=v%p;
 }
 return m;
}
Mat inv(Mat m) {Mat r=one(); for(int i=0;i<p-1;i++)r=mul(r,m); assert(mul(m,r)==one()); return r;}
Mat elem(std::array<int,6> t) {
  Mat r=one();for(int i=0;i<6;i++)r[i][i+1]=t[i]; return r;
}
Mat rim[2][2];
const int Back[3]={1,0,2};
struct Vert { int b; Mat m; };
using Key=unsigned __int128;
struct KeyHash { size_t operator()(Key k)const {return uint64_t(k) ^ (uint64_t(k >> 64)*0x9e3779b97f4a7c15ULL);}};
Key key(Vert x) {
 Key s=x.b;
 for(int i=0;i<7;i++)for(int j=i+1;j<7;j++)s=s*p+x.m[i][j];
 return s;
}
Vert step(Vert v,int port) {if(port==2)return {1-v.b,v.m};return {v.b,mul(v.m,rim[v.b][port])};}
std::unordered_multimap<Key,uint64_t,KeyHash> hits;
std::vector<Key> path;
bool dfs(Vert v,int last,int len,uint64_t w,int root) {
 if(!len){
   auto k=path.back(); auto it=hits.equal_range(k);
   for(auto i=it.first;i!=it.second;i++){
     auto other=i->second;
     bool sep=true;
     Vert z={root,one()};
     for(int t=0;t<(int)path.size()-2;t++){
       z=step(z,other%3); other/=3;
       if(std::find(path.begin()+1,path.end()-1,key(z))!=path.end()-1){sep=false;break;}
     }
     if(sep)return true;
   }
   uint64_t rev=0;for(int i=0;i<(int)path.size()-1;i++){rev=rev*3+w%3;w/=3;}
   hits.emplace(k,rev);
   return false;
 }
 for(int j=0;j<3;j++)if(last<0||Back[last]!=j){
   Vert z=step(v,j); Key k=key(z);
   if(std::find(path.begin(),path.end(),k)!=path.end())continue;
   path.push_back(k);
   if(dfs(z,j,len-1,w*3+j,root)) return true;
   path.pop_back();
 }
 return false;
}
bool blocks(int h,int b) {
 hits.clear();path={key({b,one()})};
 return dfs({b,one()},-1,h,0,b);
}
bool word(std::string s) {
 Vert v={0,one()};std::vector<Key> seen{key(v)};
 for(int i=0;i<(int)s.size();i++){
   v=step(v,s[i]-'0');auto k=key(v);
   if(i==(int)s.size()-1)return k==seen[0];
   if(std::find(seen.begin(),seen.end(),k)!=seen.end())return false;
   seen.push_back(k);
 }
 return false;
}

int main() {
 p=17;
 rim[0][0]=elem({4,4,4,10,7,1});rim[0][1]=inv(rim[0][0]);
 rim[1][0]=elem({12,12,9,12,2,0});rim[1][1]=inv(rim[1][0]);
 Mat t=rim[1][0];
 for(int k=0;k<5;++k)t=mul(mul(mul(t,rim[0][0]),inv(t)),rim[0][1]);
 std::cout<<"6th commutator (0,6): "<<t[0][6]<<"\n";
 assert(t[0][6]!=0);
 for(int h:{2,4,8,16})for(int b:{0,1}){
   if(blocks(h,b)){std::cout<<"Found forbidden simple cycle "<<2*h<<" "<<b<<"\n";return 1;}
   int duplicate=0;for(const auto &p:hits)if(hits.count(p.first)>1)duplicate++;
   std::cout<<h<<" "<<b<<" simple half-walk count "<<hits.size()<<" repeated-endpoint entries "<<duplicate<<"\n";
 }
 std::string A="21200212120212020021212120200211", B="00212121202002112120021212021202";
 std::reverse(B.begin(),B.end());for(char &p:B)p="102"[p-'0'];
 std::cout<<"C64 "<<word(A+B)<<" "<<A+B<<"\n";
}
