#include <bits/stdc++.h>
#define lli long long int
#define pb push_back
#define mod 1000000007
#pragma GCC optimize ("-O2")
#define mod2 998244353
#define MAXN 1000000000
#define v32 vector<int>
#define v64 vector<lli>
#define v1024 vector <vector <int>>
#define v4096 vector <vector <lli>>
#define vt vector
#define f(x, y, z) for (lli x = y; x < z; x++)
#define fd(x, y, z) for (lli x = y; x > z; x--)
#define lb lower_bound
#define ld long double
#define m64 map<lli,lli>
#define m32 map<int,int>
#define m64it map<lli,lli>::iterator
#define m32it map<int,int>::iterator
#define fastio ios_base::sync_with_stdio(0);cin.tie(0);cout.tie(0)
#define ist insert
#define endl "\n"
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define ordered_set tree<int, null_type,less<int>, rb_tree_tag,tree_order_statistics_node_update> 
#define p_q priority_queue 
#define min_p_q priority_queue <int,vt <int>,greater <int>>
using namespace std;
using namespace __gnu_pbds; 
template <typename T> 
void DEBUG_ARR(vt<T> a,char c)
{
	f(i,0,a.size())cout<<a[i]<<c;
	cout<<"\n";
}

int op(int a, int b){
  return __gcd(a,b);
};

inline int log2Up(int n) {
	int res = 0;
	while ((1 << res) < n) {
		res++;
	}
	return res;
}

class SqrtTree {
	private:
		int n, lg;
		vector<int> v;
		vector<int> clz;
		vector<int> layers;
		vector<int> onLayer;
		vector< vector<int> > pref;
		vector< vector<int> > suf;
		vector< vector<int> > between;
		
		void build(int layer, int lBound, int rBound) {
			if (layer >= (int)layers.size()) {
				return;
			}
			int bSzLog = (layers[layer]+1) >> 1;
			int bCntLog = layers[layer] >> 1;
			int bSz = 1 << bSzLog;
			int bCnt = 0;
			for (int l = lBound; l < rBound; l += bSz) {
				bCnt++;
				int r = min(l + bSz, rBound);
				pref[layer][l] = v[l];
				for (int i = l+1; i < r; i++) {
					pref[layer][i] = op(pref[layer][i-1], v[i]);
				}
				suf[layer][r-1] = v[r-1];
				for (int i = r-2; i >= l; i--) {
					suf[layer][i] = op(v[i], suf[layer][i+1]);
				}
				build(layer+1, l, r);
			}
			for (int i = 0; i < bCnt; i++) {
				int ans = 0;
				for (int j = i; j < bCnt; j++) {
					int add = suf[layer][lBound + (j << bSzLog)];
					ans = (i == j) ? add : op(ans, add);
					between[layer][lBound + (i << bCntLog) + j] = ans;
				}
			}
		}
	public:
		inline int query(int l, int r) {
			if (l == r) {
				return v[l];
			}
			if (l + 1 == r) {
				return op(v[l], v[r]);
			}
			int layer = onLayer[clz[l ^ r]];
			int bSzLog = (layers[layer]+1) >> 1;
			int bCntLog = layers[layer] >> 1;
			int lBound = (l >> layers[layer]) << layers[layer];
			int lBlock = ((l - lBound) >> bSzLog) + 1;
			int rBlock = ((r - lBound) >> bSzLog) - 1;
			int ans = suf[layer][l];
			if (lBlock <= rBlock) {
				ans = op(ans, between[layer][lBound + (lBlock << bCntLog) + rBlock]);
			}
			ans = op(ans, pref[layer][r]);
			return ans;
		}
		
		SqrtTree( vector<int>& v)
			: n((int)v.size()), lg(log2Up(n)), v(v), clz(1 << lg), onLayer(lg+1) {
			clz[0] = 0;
			for (int i = 1; i < (int)clz.size(); i++) {
				clz[i] = clz[i >> 1] + 1;
			}
			int tlg = lg;
			while (tlg > 1) {
				onLayer[tlg] = (int)layers.size();
				layers.push_back(tlg);
				tlg = (tlg+1) >> 1;
			}
			for (int i = lg-1; i >= 0; i--) {
				onLayer[i] = max(onLayer[i], onLayer[i+1]);
			}
			pref.assign(layers.size(), vector<int>(n));
			suf.assign(layers.size(), vector<int>(n));
			between.assign(layers.size(), vector<int>(1 << lg));
			build(0, 0, n);
		}
};
class UnionFind //rank is equal to number of vertices in a connected component
{
  public: v32 p, rank;
  // remember: vi is vector<int>
  UnionFind(int N) { rank.assign(N, 1);
  p.assign(N, 0); for (int i = 0; i < N; i++) p[i] = i; }
  int findSet(int i) { return (p[i] == i) ? i : (p[i] = findSet(p[i])); }
  bool isSameSet(int i, int j) { return findSet(i) == findSet(j); }
  void unionSet(int i, int j) 
  {
  if (!isSameSet(i, j)) {
  // if from different set
  int x = findSet(i), y = findSet(j);
  if (rank[x] > rank[y]) p[y] = x,rank[x]+=rank[y];
  // rank keeps the tree short
  else 
     {
     p[x] = y;
     rank[y]+=rank[x]; 
     }
  
  } 
 
  }   
};
class RMQv //returns max-min value in a given range
{
    public:
	struct node
    {
	int mn,mx,l,r; 
    };
	v32 h;
	vt <node> st;
	RMQv(v32 a)
	{
       h=a;
       st.resize(4*h.size());
       build(0,h.size()-1);
	}
	void build(int l,int r,int k=0)
	{
		st[k].l=l,st[k].r=r;
	    if(l==r)
		   {st[k].mx=st[k].mn=h[l];
             return;
		   }
	    build(l,(l+r)>>1,2*k+1);
	    build(((l+r)>>1)+1,r,2*k+2);
      st[k].mx=max(st[2*k+1].mx,st[2*k+2].mx); 
	}
	int maxquery(int l,int r,int k=0)
    {
       if(l>r)return -MAXN;
       int ll=st[k].l,rr=st[k].r,mid=(ll+rr)>>1;
       if(r<ll || l>rr)return -MAXN;
       if(ll>=l && rr<=r)
          return st[k].mx;
   	   int ans=-MAXN;   
   	   ans=maxquery(l,r,2*k+1);
   	   ans=max(ans,maxquery(l,r,2*k+2));
   	   return ans;     
    }
    void update(int id,int val,int k=0)
    {
        int l=st[k].l,r=st[k].r,mid=(l+r)>>1;
        if(id<l || id>r)return;
        if(l==r)
        {
            st[k].mx=val;
            return;
        }
        update(id,val,2*k+1);
        update(id,val,2*k+2);
        st[k].mx=max(st[2*k+1].mx,st[2*k+2].mx); 
    }
};
class RMQ  //gives index of min-max in a given range
{
    public:
	struct node
    {
	int mx,l,r; 
    };
	v32 h;
	vt <node> st;
	RMQ(v32 a)
	{
       h=a;
       st.resize(4*h.size());
       build(0,h.size()-1);
	}
	void build(int l,int r,int k=0)
	{
		st[k].l=l,st[k].r=r;
	    if(l==r)
		   {st[k].mx=l;
             return;
		   }
	    build(l,(l+r)>>1,2*k+1);
	    build(((l+r)>>1)+1,r,2*k+2);	
      if(h[st[2*k+1].mx]>=h[st[2*k+2].mx])
	    st[k].mx=st[2*k+1].mx;
	    else st[k].mx=st[2*k+2].mx;
	}
	int maxquery(int l,int r,int k=0)
    {
       int ll=st[k].l,rr=st[k].r,mid=(ll+rr)>>1;
       if(r<ll || rr<l)return -1; 
       if(ll>=l && rr<=r)
          return st[k].mx;
   	      int p1=maxquery(l,r,2*k+1);
   	      int p2=maxquery(l,r,2*k+2);
       if(p1==-1)return p2;
       if(p2==-1)return p1;
       if(h[p1]>=h[p2])return p1;
       return p2;      
    }
    void update(int id,int val,int k=0)
    {
        int l=st[k].l,r=st[k].r,mid=(l+r)>>1;
        if(id<l || id>r)return;
        if(l==r)
        {
            h[l]=val;
            return;
        }
        update(id,val,2*k+1);
        update(id,val,2*k+2);	
      if(h[st[2*k+1].mx]>=h[st[2*k+2].mx])
	    st[k].mx=st[2*k+1].mx;
	    else st[k].mx=st[2*k+2].mx;
    }
};
class LAZY //currently set to set a given range by a value
{
   public:
   struct node
   {
    int l,r,lazy=0;lli lazyval=0;
    lli sum=0;
   };	
   vt <node> st;v32 h;
   LAZY(v32 a)
   { 
   	  h=a;
   	  st.resize(4*h.size());
   	  cst(0,h.size()-1);
   }	
   void cst(int l,int r,int k=0)
   {
    st[k].l=l,st[k].r=r;
    if(l==r)
        { 
          st[k].sum=h[l];   
          return;
        }
    cst(l,(l+r)/2,2*k+1);
    cst((l+r)/2+1,r,2*k+2);
    st[k].sum=st[2*k+1].sum+st[2*k+2].sum;    
   }
   void shift(int k)
   {
   st[k].sum=(st[k].r-st[k].l+1)*st[k].lazyval;
   if(st[k].l!=st[k].r){
      st[2*k+1].lazyval=st[k].lazyval;
      st[2*k+2].lazyval=st[k].lazyval;
      st[2*k+1].lazy=st[2*k+2].lazy=1;
   }
   st[k].lazyval=0;
   st[k].lazy=0;      
   }
   lli query(int l,int r,int k=0)
   {
	  if(st[k].lazy) shift(k);
    int ll=st[k].l,rr=st[k].r;
    if(ll>r || rr<l)return 0;
    if(ll>=l && rr<=r)
    return st[k].sum;
    return query(l,r,2*k+1)+query(l,r,2*k+2);     
   }
   void update(int l,int r,lli x,int k=0)
   {
   int ll=st[k].l,rr=st[k].r;
   if(ll>r || rr<l)return ;
   if(ll>=l && rr<=r){
     st[k].lazyval=x;
     st[k].lazy=1;      
     return;
    }
    if(st[k].lazy) shift(k);
    if(ll==rr) return;
    update(l,r,x,2*k+1);
    update(l,r,x,2*k+2);
    if(st[2*k+1].lazy)  shift(2*k+1);
    if(st[2*k+2].lazy)  shift(2*k+2);
    st[k].sum=st[2*k+1].sum+st[2*k+2].sum;           
   }
   int lower_bound(int l,int r,int val)
   {
    while(l!=r)
    {
      int mid=(l+r)/2;
      if(query(mid,mid)>=val)
        r=mid;
      else 
        {l=mid+1;
         if(mid+1<h.size())  
             if(query(mid+1,mid+1)>val)
             {
              l=mid;
              break;
             }
        }
    }
    return l;
   }
};
class span
{
  public:
	v32 a;
	span()
	{};
	v32 max_left_border_without_equality()
     {
	int n=a.size();
	v32 ta,al(n);
	f(i,0,n)
    {
  	  if(ta.size()==0)
  		{
  			ta.pb(i);
  			al[i]=i;
  		}
  	  else
  	  {
  		while(a[i]>a[ta[ta.size()-1]]) {ta.pop_back();if(ta.size()==0)break;}
  		 if(ta.size()==0)
  		 {
  		    ta.pb(i);
  			al[i]=0;	
  		 }
  		 else
  		 {
  		 	al[i]=ta[ta.size()-1]+1;
  		 	ta.pb(i);
  		 }
  	  }
  	}
  	return al; 
     }
    v32 max_left_border_with_equality()
     {
	int n=a.size();
	v32 ta,al(n);
	f(i,0,n)
    {
  	  if(ta.size()==0)
  		{
  			ta.pb(i);
  			al[i]=i;
  		}
  	  else
  	  {
  		while(a[i]>=a[ta[ta.size()-1]]) {ta.pop_back();if(ta.size()==0)break;}
  		 if(ta.size()==0)
  		 {
  		    ta.pb(i);
  			al[i]=0;	
  		 }
  		 else
  		 {
  		 	al[i]=ta[ta.size()-1]+1;
  		 	ta.pb(i);
  		 }
  	  }
  	}
  	return al; 
     }
    v32 min_left_border_without_equality()
     {
	int n=a.size();
	v32 ta,al(n);
	f(i,0,n)
    {
  	  if(ta.size()==0)
  		{
  			ta.pb(i);
  			al[i]=i;
  		}
  	  else
  	  {
  		while(a[i]<a[ta[ta.size()-1]]) {ta.pop_back();if(ta.size()==0)break;}
  		 if(ta.size()==0)
  		 {
  		    ta.pb(i);
  			al[i]=0;	
  		 }
  		 else
  		 {
  		 	al[i]=ta[ta.size()-1]+1;
  		 	ta.pb(i);
  		 }
  	  }
  	} 
  	return al;
     }
    v32 min_left_border_with_equality()
     {
	int n=a.size();
	v32 ta,al(n);
	f(i,0,n)
    {
  	  if(ta.size()==0)
  		{
  			ta.pb(i);
  			al[i]=i;
  		}
  	  else
  	  {
  		while(a[i]<=a[ta[ta.size()-1]]) {ta.pop_back();if(ta.size()==0)break;}
  		 if(ta.size()==0)
  		 {
  		    ta.pb(i);
  			al[i]=0;	
  		 }
  		 else
  		 {
  		 	al[i]=ta[ta.size()-1]+1;
  		 	ta.pb(i);
  		 }
  	  }
  	} 
  	return al;
     }
    v32 max_right_border_without_equality()
     {
	int n=a.size();
	reverse(a.begin(),a.end());
	v32 ans=max_left_border_without_equality();
	reverse(ans.begin(),ans.end());
	f(i,0,n)ans[i]=n-1-ans[i];
	reverse(a.begin(),a.end());
	return ans;
     }
    v32 max_right_border_with_equality()
     {
	int n=a.size();
	reverse(a.begin(),a.end());
	v32 ans=max_left_border_with_equality();
	reverse(ans.begin(),ans.end());
	f(i,0,n)ans[i]=n-1-ans[i];
	reverse(a.begin(),a.end());
	return ans;
     } 
    v32 min_right_border_without_equality()
     {
	int n=a.size();
	reverse(a.begin(),a.end());
	v32 ans=min_left_border_without_equality();
	reverse(ans.begin(),ans.end());
	f(i,0,n)ans[i]=n-1-ans[i];
	reverse(a.begin(),a.end());
	return ans;
     }
     v32 min_right_border_with_equality()
     {
	int n=a.size();
	reverse(a.begin(),a.end());
	v32 ans=min_left_border_with_equality();
	reverse(ans.begin(),ans.end());
	f(i,0,n)ans[i]=n-1-ans[i];
	reverse(a.begin(),a.end());
	return ans;
     }

};
class merge_sort_tree
{
  public:
	lli cnt(lli x,vector <int> &arr)
    {
     lli n=arr.size();
     vector<int>::iterator low,high;
     low = lower_bound(arr.begin(), arr.end(), x);
     if (low == (arr.end()) || *low != x)
     return 0;
     high = upper_bound(low, arr.end(), x);
     return high - low;
    }
    lli get_last_smaller(vector<int>& v, int x)
    {
     lli first = 0, last = v.size()-1;
     while (first <= last)
     {
       lli mid = (first + last) / 2;
       if (v[mid] >= x)
       last = mid - 1;
       else
       first = mid + 1;
     }
  return first - 1 < 0 ? -1 : first - 1;
    }
	struct node
    {
      int l,r;
      vector <pair<int,int>> arr;
      v32 arr2;
    };
	v32 a;
    vt <node> st; 
	
    merge_sort_tree(v32 b)
    {
      st.resize(4*b.size());
      a=b;
      build(0,b.size()-1);
    }
     void build(int l,int r,int k=0)
      {
        st[k].l=l,st[k].r=r;
        for(int i=l;i<r+1;i++)
        st[k].arr.push_back({a[i],i});
        sort(st[k].arr.begin(),st[k].arr.end());
        f(i,0,st[k].arr.size())st[k].arr2.pb(st[k].arr[i].first);
        if(l==r)
        return;
        build(l,(l+r)/2,2*k+1);
        build((l+r)/2+1,r,2*k+2);
      }
    lli count_val_in_range(int l,int r,int t,int k=0)
    {
     if(l>r)return 0;
     int ll=st[k].l,rr=st[k].r,mid=(ll+rr)/2;
     if(ll>r || l>rr)return 0;
     if(ll>=l && rr<=r) return cnt(t,st[k].arr2);
     return count_val_in_range(l,r,t,2*k+1)+count_val_in_range(l,r,t,2*k+2);
    }
    lli count_vals_less_than_given_val(int l,int r,int t,int k=0)
    {
     if(l>r)return 0;
     int ll=st[k].l,rr=st[k].r,mid=(ll+rr)/2;
     if(l>rr || ll>r)return 0;
     if(ll>=l && rr<=r) return get_last_smaller(st[k].arr2,t)+1;
     lli ans=0;
     return count_vals_less_than_given_val(l,r,t,2*k+1)+count_vals_less_than_given_val(l,r,t,2*k+2);   
    }	
    int find(int l,int r,int x,int k=0)
    {
     if(l>r)return -1;
     int ll=st[k].l,rr=st[k].r,mid=(ll+rr)/2;
     if(l>rr || ll>r)return -1;
     if(ll>=l && rr<=r)
       { 
         int p=lower_bound(st[k].arr2.begin(), st[k].arr2.end(), x)-st[k].arr2.begin();
         if(p==st[k].arr2.size())return -1;
         if(st[k].arr2[p]==x)return st[k].arr[p].second;
         return -1;
       }
     int x2,y2;
     x2=find(l,r,x,2*k+1);
     y2=find(l,r,x,2*k+2);
     if(x==-1)return y2;
     if(y==-1)return x2;
     return x2;
    }
};
lli tmod(lli x,lli m){return (x%m+m)%m;}//USE AT YOUR OWN RISK
lli power(lli x, lli y) 
{
    lli res = 1;  
   
    while (y > 0) 
    { 
        if (y & 1) 
            res = (res*x)%mod; 
        y = y>>1; 
        x = (x*x)%mod;  
    }
    if(res<0)
       res+=mod; 
    return res; 
}
lli modInverse(lli a, lli m) 
{
    lli m0 = m; 
    lli y = 0, x = 1; 
    if (m == 1) 
      return 0; 
  
    while (a > 1) 
    {  
        lli q = a / m; 
        lli t = m; 
        m = a % m, a = t; 
        t = y; 
        y = x - q * y; 
        x = t; 
    }  
    if (x < 0) 
       x += m0; 
    return x; 
} 
class matrix
{
public:
  v4096 m;
  v4096 I;
  matrix(v4096 x){
    m=x;
    I=x;
    f(i,0,m.size())I[i][i]=1;
    f(i,0,x.size())f(j,0,x.size())if(i!=j)I[i][j]=0;
  };
  v4096 multiply(v4096 m1,v4096 m2)
  {
    v4096 m3=m1;
    f(i,0,m2.size())
      {
          f(j,0,m2[0].size())
          {    
            m3[i][j]=0;
            f(k,0,m1[0].size()) m3[i][j]=(m3[i][j]+m1[i][k]*m2[k][j])%mod;
          }
      }
      return m3;
  }
  v4096 exp(lli p)
   {
    v4096 res;
   if(p==1)
      return m;
   if(p==0) return I;
      if(p%2==0)
      {
          res=exp(p/2);
          res=multiply(res,res);
      }
      else
      {
          res=exp(p/2);
          res=multiply(res,res);
          res=multiply(res,m);
      }
   return res;
   }
};

int main() 
{ 
  fastio;
  
  return 0; 	
}
