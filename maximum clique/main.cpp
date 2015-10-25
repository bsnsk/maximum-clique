//
//  main.cpp
//  maximum clique
//
//  Created by Inability on 14-5-24.
//  Copyright (c) 2014年 Inability. All rights reserved.
//

#include <cstdio>
#include <cassert>
#include <cstdlib>
#include <ctime>
#include <cstring>
#include <vector>
#include <set>
#include <map>
#include <algorithm>

using namespace std;

//  ================= parameters that can be modified =================
const int maxn = 4010 + 1, maxm = 8000000;

const int delta = 2, maxstep = 10000000;
//  ===================================================================

int n, m, E(1), first[maxn], nxt[maxm*2], to[maxm*2];

int age[maxm], weight[maxm];
int dscore[maxn];

char st[20];

bool inL[maxm], inC[maxn], tmp[maxn];
bool original_G[maxn][maxn];

unsigned START_TIME = (unsigned)clock();

class cmp_age {
public:
	inline bool operator ()(int e1, int e2){
		return (age[e1] != age[e2]) ? (age[e1] < age[e2]) : (e1 < e2);
	}
};

class cmp_dscore {
public:
	inline bool operator ()(int v1, int v2){
		return (dscore[v1] != dscore[v2]) ? (dscore[v1] > dscore[v2]) : (v1 < v2);
	}
};

set <int, class cmp_age> L, UL;
set <int, class cmp_dscore> C, C_ans;
map < pair <int, int>, int> edge_num;

pair<int, int> last_chosen;

int cnt_edges[maxn];
bool in_heap[maxn];
int *heap_weight, heap_place[maxn], heap_array[maxn], heap_len;

void add_edge(int u, int v){
	nxt[++E] = first[u]; to[E] = v; first[u] = E;
}

int calc_dscore(int u){
	int re=0;
	for (int i=first[u]; i; i=nxt[i])
		if (!inC[to[i]])
			re += weight[i/2];
	return inC[u] ? -re : re;
}

inline int calc_score(int u, int v){
	assert(inC[u] && !inC[v]);
	map < pair <int, int>, int> :: iterator it;
	if (it=edge_num.find(make_pair(u, v)), it!=edge_num.end())
		return dscore[u] + dscore[v] + weight[it->second];
	return dscore[u] + dscore[v];
}

#define F(x) ((x)>>1)
#define L(x) ((x)<<1)
#define R(x) (((x)<<1)+1)

void heap_up(int x){
	for (; x>1 && heap_weight[heap_array[F(x)]] < heap_weight[heap_array[x]]; x>>=1) {
		swap(heap_array[F(x)], heap_array[x]);
		swap(heap_place[heap_array[F(x)]], heap_place[heap_array[x]]);
	}
}

void heap_down(int x){
	for (int ma; L(x)<=heap_len; x=ma) {
		ma = (L(x)==heap_len) ? L(x) : (heap_weight[heap_array[L(x)]] > heap_weight[heap_array[R(x)]] ? L(x) : R(x));
		if (heap_weight[heap_array[ma]] <= heap_weight[heap_array[x]])
			break;
		swap(heap_array[ma], heap_array[x]);
		swap(heap_place[heap_array[ma]], heap_place[heap_array[x]]);
	}
}

int heap_pop(){
	assert(heap_len > 0);
	int re = heap_array[1];
	heap_array[1] = heap_array[heap_len];
	heap_place[heap_array[1]] = 1;
	in_heap[re] = 0;
	heap_len --;
	heap_down(1);
	return re;
}

void heap_clear(){
	heap_len=0;
	memset(in_heap, 0, sizeof(in_heap));
}

void heap_push(int x){
	heap_array[++heap_len]=x;
	heap_place[x]=heap_len;
	in_heap[x] = 1;
	heap_up(heap_len);
}

void check_edge(set<int, cmp_age>::iterator it, vector < pair<int, int> > &S){
	for (set <int>::iterator itc=C.begin(); itc!=C.end(); ++itc) {
		if (calc_score(*itc, to[(*it)*2])>0)
			S.push_back(make_pair(*itc, to[(*it)*2]));
		if (calc_score(*itc, to[(*it)*2+1])>0)
			S.push_back(make_pair(*itc, to[(*it)*2+1]));
	}
}

bool equal_pair(const pair<int, int> &a, const pair<int, int> &b){
	return (a.first==b.first && a.second==b.second) || (a.first==b.second && a.second==b.first);
}

bool choose_pair(int &u, int &v){
	vector < pair<int, int> > S;
	if (L.begin()!=L.end())
		check_edge(L.begin(), S);
	if (!S.empty() && (S.size()>1 || !equal_pair(*S.begin(), last_chosen))) {
		for (int d; d= rand()%S.size(), u = S[d].first, v = S[d].second, equal_pair(make_pair(u, v), last_chosen););
		return 1;
	}
	for (set<int, cmp_age>::iterator it=UL.begin(), nxt_it; it!=UL.end(); it=nxt_it) {
		check_edge(it, S);
		++ (nxt_it = it);
		UL.erase(it);
		if (!S.empty() && (S.size()>1 || !equal_pair(*S.begin(), last_chosen))) {
			for (int d; d= rand()%S.size(), u = S[d].first, v = S[d].second, equal_pair(make_pair(u, v), last_chosen););
			return 1;
		}
	}
	//fprintf(stderr, "choose failed.\n");
	return 0;
}

void vertex_remove(int u, int step, bool heap_op=0){
	assert(inC[u]);
	inC[u] = 0;
	dscore[u] = -dscore[u];
	C.erase(u);
	for (int i=first[u]; i; i=nxt[i]) {
		if (!inC[to[i]]) {
			inL[i/2]=1;
			age[i/2] = step;
			L.insert(i/2);
			UL.insert(i/2);
			dscore[to[i]] = calc_dscore(to[i]);
		}
		else {
			C.erase(to[i]);
			dscore[to[i]] = calc_dscore(to[i]);
			C.insert(to[i]);
		}
		if (heap_op && in_heap[to[i]]){
			heap_up(heap_place[to[i]]);
			heap_down(heap_place[to[i]]);
		}
	}
}

void vertex_add(int u, bool heap_op=0){
	assert(!inC[u]);
	inC[u] = 1;
	assert(calc_dscore(u) + dscore[u] == 0);
	dscore[u] = -dscore[u];
	C.insert(u);
	for (int i=first[u]; i; i=nxt[i]) {
		if (!inC[to[i]]) {
			inL[i/2]=0;
			L.erase(i/2);
			UL.erase(i/2);
			dscore[to[i]] = calc_dscore(to[i]);
		}
		else {
			C.erase(to[i]);
			dscore[to[i]] = calc_dscore(to[i]);
			C.insert(to[i]);
		}
		if (heap_op && in_heap[to[i]]){
			heap_up(heap_place[to[i]]);
			heap_down(heap_place[to[i]]);
		}
	}
}

void initialize_greedily(){
	heap_clear();
	heap_weight = dscore;
	for (int i=1; i<=n; i++) {
		heap_push(i);
	}
	for (int p; L.size()>0; ) {
		p=heap_pop();
		vertex_add(p, 1);
	}
	fprintf(stderr, "initialization res: C.size=%d, L.size=%d\n", (int)C.size(), (int)L.size());
}

// remove some vertices(highest dscore) from C until |C|=ub-delta
void remove_vertices(int step, int ub){
	heap_clear();
	heap_weight = dscore;
	for (int i=1; i<=n; i++)
		if (inC[i])
			heap_push(i);
	while (C.size() > ub-delta)
		vertex_remove(heap_pop(), step, 1);
}

void print_current_result(int step){
	FILE *ou = fopen("res.txt", "w");
	fprintf(ou, "Maximum Clique Size: %d\nTime: %.3lf s\n", n-(int)(C_ans.size()), (clock()-START_TIME)*1./CLOCKS_PER_SEC);
	fprintf(ou, "Step: %d\n", step);
	fprintf(ou, "delta: %d\n", delta);
	fprintf(ou, "%d Vertices, %d edges\n", n, n*(n-1)/2-m);
	printf("Maximum Clique Size: %d\nTime: %.3lf s\n", n-(int)(C_ans.size()), (clock()-START_TIME)*1./CLOCKS_PER_SEC);
	
	memset(tmp, 0, sizeof(tmp));
	for (set<int>::iterator it=C_ans.begin(); it!=C_ans.end(); ++it)
		tmp[*it] = 1;
	
	fprintf(ou, "Maximum Clique:\n");
	for (int i=1; i<=n; i++)
		if (!tmp[i])
			fprintf(ou, "%d\n", i);
	fclose(ou);
}

int calc_mvc(){
	int step = 0;
	L.clear(), UL.clear();
	memset(inC, 0, sizeof(inC));
	memset(inL, 0, sizeof(inL));
	for (int i=1; i<=m; i++) {
		L.insert(i);
		UL.insert(i);
		inL[i] = 1;
		weight[i] = 1;
	}
	for (int i=1; i<=n; i++)
		dscore[i] = calc_dscore(i);
	initialize_greedily();
	int ub = (int)C.size();
	C_ans = C;
	fprintf(stderr, "after greed initialization, C.size=%d\n", (int)C.size());
	remove_vertices(0, ub);
	
	for (int u, v; step < maxstep; step++) {
		if (L.size()){
			if (!choose_pair(u, v)){
			
				// update edge weight
				for (int i=1; i<=m; i++)
					if (inL[i])
						weight[i] ++;
				for (int i=1; i<=n; i++)
					dscore[i] = calc_dscore(i);
			
				// random u,v
				int pu=rand()%(C.size());
				for (int i=0, j=0; i<=n && j<=pu; ) {
					while (!inC[++i]);
					if (j++==pu)
						u=i;
				}
				int pla=rand()%L.size();
				for (int i=0, j=0; i<=m && j<=pla; ) {
					while (!inL[++i]);
					if (j++==pla)
						v=to[i*2+(rand()&1)];
				}
				//fprintf(stderr, "random step %d,%d\n", u, v);
			}
			vertex_remove(u, step);
			vertex_add(v);
			last_chosen = make_pair(u, v);
		}
		
		//fprintf(stderr, "after exchange, C.size=%d\n", (int)C.size());
		if (C.size() + L.size() < ub) {
			//ub = (int)(C.size() + L.size());
			C_ans = C;
			if (!L.empty()) {
				// greedily (choose vertices that covers most edges) extend C_ans to a vertex cover
				heap_clear();
				int left_edges=(int)L.size();
				heap_weight = cnt_edges;
				for (int i=1; i<=n; i++) {
					if (!inC[i]) {
						cnt_edges[i]=0;
						for (int e=first[i]; e; e=nxt[e])
							if (inL[e/2])
								cnt_edges[i]++;
						heap_push(i);
					}
				}
				while (left_edges>0) {
					int now = heap_pop();
					C_ans.insert(now);
					for (int e=first[now]; e; e=nxt[e])
						if (inL[e/2] && in_heap[to[e]]) {
							cnt_edges[to[e]]--;
							left_edges --;
							heap_down(heap_place[to[e]]);
						}
				}
			}
			assert(C_ans.size()<=L.size()+C.size());
			ub = (int)C_ans.size();
			print_current_result(step);
		}
		remove_vertices(step, ub);
		if (step % 1000 == 0)
			fprintf(stderr, "step: %d. mvc: %d. C.size=%d\n", step, (int)C_ans.size(), (int)C.size());
	}
	return (int)C_ans.size();
}

int main(int argc, const char * argv[]){
	
	srand((unsigned)time(0));
	
	FILE *in = fopen("data.txt", "rb");
	while (fscanf(in, "%s", st), st[0]=='c' && !st[1])
		while (st[0]=getc(in), st[0]!='\n');
	
	fscanf(in, "%*s%d%d", &n, &m);
	assert(n<maxn && n*(n-1)/2-m<maxm);
	for (int i=1, j, k; i<=m; i++) {
		fscanf(in, "%*s%d%d", &j, &k);
		original_G[j][k]=1;
	}
	m = 0;
	for (int k=1; k<=n; k++)
		for (int j=k+1; j<=n; j++)
			if (!original_G[k][j]) {
				add_edge(j, k);
				add_edge(k, j);
				edge_num[make_pair(j, k)] = ++m;
				edge_num[make_pair(k, j)] = m;
			}
	
	calc_mvc();
	
	fclose(in);
    return 0;
}

