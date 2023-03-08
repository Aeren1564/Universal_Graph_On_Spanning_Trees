#include <bits/stdc++.h>
using namespace std;
#if __cplusplus > 201703L
#include <ranges>
using namespace numbers;
#endif

vector<array<int, 2>> generate_tree(auto &&rng, int n){
	vector<array<int, 2>> res;
	if(n <= 3 || rng() & 1){
		vector<int> label(n);
		iota(label.begin(), label.end(), 0);
		shuffle(label.begin(), label.end(), rng);
		for(auto u = 1; u < n; ++ u) res.push_back({label[rng() % u], label[u]});
		shuffle(res.begin(), res.end(), rng);
	}
	else{
		vector<int> prufer(n - 2), deg(n, 1);
		for(auto &u: prufer) ++ deg[u = rng() % n];
		int leaf = find(deg.begin(), deg.end(), 1) - deg.begin(), u = leaf;
		for(auto v: prufer){
			res.push_back({min(leaf, v), max(leaf, v)});
			if(-- deg[v] == 1 && v < u) leaf = v;
			else{
				u = find(deg.begin() + u + 1, deg.end(), 1) - deg.begin();
				leaf = u;
			}
		}
		res.push_back({leaf, n - 1});
	}
	return res;
}

struct admissible_graph{
	int n;
	vector<array<int, 2>> next;
	vector<int> size, pv;
	admissible_graph(int n): n(n){
		assert(n >= 1);
		auto build = [&](auto self, int n)->int{
			if(!n) return -1;
			int u = (int)next.size();
			next.push_back({-1, -1});
			size.push_back(n);
			pv.push_back(-1);
			if(n == 1) return u;
			int k = __lg(n), left = min(n, 1 << k) - 1;
			next[u][0] = self(self, left);
			pv[next[u][0]] = u;
			if(left + 1 == n) return u;
			next[u][1] = self(self, n - left - 1);
			pv[next[u][1]] = u;
			return u;
		};
		build(build, n);
	}
	// -1: root, 0: left, 1: right
	// O(1)
	int side(int u) const{
		assert(0 <= u && u < n);
		return u ? next[pv[u]][1] == u : -1;
	}
	// Construction in http://www.math.ucsd.edu/~fan/mypaps/fanpap/fc35universal_trees.pdf
	// O(n * log(n)) edges
	vector<array<int, 2>> get_edge_wrong() const{
		vector<array<int, 2>> res;
		vector<int> q(n);
		for(auto u = 0; u < n; ++ u){
			int beg = 0, end = 0;
			for(auto i = 0; i < 2; ++ i) if(~next[u][i]) q[end ++] = next[u][i];
			if(~pv[u]){
				int p = pv[u];
				if(next[p][1] == u) q[end ++] = next[p][0];
				if(~pv[p]){
					int pp = pv[p];
					if(next[pp][1] == p) q[end ++] = next[pp][0];
				}
			}
			while(beg < end){
				int v = q[beg ++];
				res.push_back({u, v});
				for(auto i = 0; i < 2; ++ i) if(~next[v][i]) q[end ++] = next[v][i];
			}
		}
		return res;
	}
	// Corrected version
	// O(n * log(n)^2) edges
	vector<array<int, 2>> get_edge() const{
		vector<array<int, 2>> res;
		vector<int> q(n), path;
		for(auto u = 0; u < n; ++ u){
			int beg = 0, end = 0;
			for(auto i = 0; i < 2; ++ i) if(~next[u][i]) q[end ++] = next[u][i];
			path.clear();
			for(auto w = u; w; w = pv[w]){
				path.push_back(next[pv[w]][1] == w);
				if(!path.back()) continue;
				int v = pv[w];
				for(auto i = (int)path.size() - 1; i >= 0; -- i) v = next[v][!path[i]];
				q[end ++] = (int)path.size() >= 2 ? pv[v] : v;
			}
			while(beg < end){
				int v = q[beg ++];
				res.push_back({u, v});
				for(auto i = 0; i < 2; ++ i) if(~next[v][i]) q[end ++] = next[v][i];
			}
		}
		return res;
	}
	// tr must be a tree
	// Returns an embedding E such that G - E(tr) is admissible.
	// O(n^2 + m^2)
	vector<int> embed(vector<vector<int>> tree){
		int m = (int)tree.size();
		assert(1 <= m && m <= n);
		auto erase = [&](vector<int> &a, int x)->void{
			auto it = find(a.begin(), a.end(), x);
			assert(it != a.end() && *it == x);
			a.erase(it);
		};
		auto cut = [&](vector<int> &tree_vertices, int u)->void{
			erase(tree_vertices, u);
			for(auto v : tree[u]) erase(tree[v], u);
			for(auto i = 1; i < (int)tree[u].size(); ++i) {
				int x = tree[u][0], y = tree[u][i];
				tree[x].insert(find(tree[x].begin(), tree[x].end(), y), y);
				tree[y].insert(find(tree[y].begin(), tree[y].end(), x), x);
			}
			tree[u].clear();
		};
		vector<int> tree_size(n);
		auto get_small_subtrees = [&](const vector<int> &tree_vertices, int k)->pair<int, vector<int>>{
			assert(1 <= k && k < (int)tree_vertices.size());
			if((int)tree_vertices.size() == k + 1) return {tree_vertices[0], tree[tree_vertices[0]]};
			int root = -1;
			for(auto u: tree_vertices){
				tree_size[u] = 1;
				if(!~root && (int)tree[u].size() == 1) root = u;
			}
			assert(~root);
			auto dfs = [&](auto self, int u, int p)->void{
				for(auto v: tree[u]) if(v != p){
					self(self, v, u);
					tree_size[u] += tree_size[v];
				}
			};
			dfs(dfs, root, -1);
			for(auto u = tree[root][0]; ;){
				assert(tree_size[u] >= k + 1);
				int big = -1;
				for(auto v: tree[u]){
					if(v == root) continue;
					if(tree_size[v] == k) return {u, {v}};
					if(tree_size[v] >= k + 1){
						big = v;
						break;
					}
				}
				if(!~big){
					vector<int> a = tree[u];
					erase(a, root);
					int sum = accumulate(a.begin(), a.end(), 0, [&](int x, int u){ return x + tree_size[u]; });
					while(sum >= 2 * k){
						sum -= tree_size[a.back()];
						a.pop_back();
					}
					return {u, a};
				}
				root = u;
				u = big;
			}
			assert(false);
		};
		vector<int> was(n);
		auto cut_small_subtrees = [&](const vector<int> &tree_vertices, int k)->array<vector<int>, 2>{
			auto [u, roots] = get_small_subtrees(tree_vertices, k);
			static int it = 0;
			++ it;
			vector<int> small{u}, large;
			was[u] = it;
			for(auto r: roots){
				auto dfs = [&](auto self, int u)->void{
					was[u] = it;
					small.push_back(u);
					for(auto v: tree[u]) if(was[v] != it) self(self, v);
				};
				dfs(dfs, r);
			}
			int w = -1;
			for(auto v: tree[u]) if(was[v] != it){
				if(~w){
					tree[w].push_back(v);
					tree[v].push_back(w);
				}
				else w = v;
				erase(tree[v], u);
			}
			tree[u].erase(remove_if(tree[u].begin(), tree[u].end(), [&](int v){ return was[v] != it; }), tree[u].end());
			for(auto v: tree_vertices) if(was[v] != it) large.push_back(v);
			return {small, large};
		};
		vector<int> mapped(n, false);
		vector<int> res(m, -1);
		// tree vertex, graph vertex
		auto set_res = [&](int u, int v)->void{
			assert(0 <= u && u < m);
			assert(0 <= v && v < n);
			assert(!~res[u]);
			assert(!mapped[v]);
			res[u] = v;
			mapped[v] = true;
		};
		// graph vertex
		auto valid = [&](int u)->bool{
			return ~u && !mapped[u];
		};
		// graph vertex
		vector<int> q(n);
		auto get_size = [&](int u)->int{
			assert(~u && valid(u));
			int res = 0;
			q[0] = u;
			for(auto end = 1; res < end; ){
				int u = q[res ++];
				for(auto i = 0; i < 2; ++ i) if(valid(next[u][i])) q[end ++] = next[u][i];
			}
			return res;
		};
		auto solve = [&](auto self, int root, int u, vector<int> tree_vertices)->void{
			int m = (int)tree_vertices.size();
			assert(~root);
			int root_size = get_size(root), left = next[root][0], right = next[root][1];
			assert(1 <= m && m <= root_size);
			assert(find(tree_vertices.begin(), tree_vertices.end(), u) != tree_vertices.end());
			if(m == 1){
				while(true){
					if(valid(next[root][1])) root = next[root][1];
					else if(valid(next[root][0])) root = next[root][0];
					else break;
				}
				set_res(u, root);
			}
			else if(!valid(right)){
				assert(valid(left));
				if(m < root_size){
					self(self, left, u, tree_vertices);
				}
				else{
					assert(m == root_size);
					cut(tree_vertices, u);
					self(self, left, tree_vertices[0], tree_vertices);
					set_res(u, root);
				}
			}
			else{
				assert(valid(left) && valid(right));
				int right_size = get_size(right);
				if(m <= right_size){
					self(self, right, u, tree_vertices);
				}
				else{
					if(right_size == 1){
						cut(tree_vertices, u);
						set_res(u, right);
						self(self, root, tree_vertices[0], tree_vertices);
					}
					else if(!valid(next[right][1])){
						assert(valid(next[right][0]));
						if(m < root_size){
							cut(tree_vertices, u);
							auto [small, large] = cut_small_subtrees(tree_vertices, get_size(next[right][0]));
							{
								auto _nextright = next[right];
								next[right] = { next[left][1], next[right][0] };
								self(self, right, small[0], small);
								next[right] = _nextright;
							}
							set_res(u, right);
							if(!large.empty()) self(self, root, large[0], large);
						}
						else{
							assert(m == root_size);
							cut(tree_vertices, u);
							self(self, root, tree_vertices[0], tree_vertices);
							set_res(u, root);
						}
					}
					else{
						assert(valid(left) && valid(right));
						if(m < root_size){
							cut(tree_vertices, u);
							auto[small, large] = cut_small_subtrees(tree_vertices, get_size(next[right][1]));
							{
								self(self, right, small[0], small);
							}
							if(!large.empty()){
								if(valid(next[right][0])){
									auto[small2, large2] = cut_small_subtrees(large, get_size(next[right][0]));
									{
										auto _nextright = next[right];
										next[right] = {next[left][1], next[right][0]};
										self(self, right, small2[0], small2);
										next[right] = _nextright;
									}
									set_res(u, right);
									if(!large2.empty()){
										self(self, root, large2[0], large2);
									}
								}
								else{
									set_res(u, right);
									self(self, root, large[0], large);
								}
							}
						}
						else{
							assert(m == root_size);
							cut(tree_vertices, u);
							self(self, root, tree_vertices[0], tree_vertices);
							set_res(u, root);
						}
					}
				}
			}
		};
		vector<int> tree_vertices(m);
		iota(tree_vertices.begin(), tree_vertices.end(), 0);
		solve(solve, 0, 0, tree_vertices);
		assert(*min_element(res.begin(), res.end()) >= 0);
		return res;
	}
};

int main(){
	cin.tie(0)->sync_with_stdio(0);
	unsigned int random_seed = 123456;
	mt19937 rng(random_seed);
	// Size of the graph
	int n = 12;
	// Set to true to construct the corrected graph
	bool corrected = false;
	// Admissible graph on n vertices
	admissible_graph AG(n);
	vector<array<int, 2>> edge;
	if(corrected){
		edge = AG.get_edge();
	}
	else{
		edge = AG.get_edge_wrong();
	}
	for(auto &[u, v]: edge){
		if(u > v){
			swap(u, v);
		}
	}
	sort(edge.begin(), edge.end());
	for(auto _tc_num = 0; ; ++ _tc_num){
		// Random tree on m vertices
		int m = rng() % n + 1;
		vector<array<int, 2>> tree_edge = generate_tree(rng, m);
		vector<vector<int>> tree(m);
		for(auto [u, v]: tree_edge){
			tree[u].push_back(v);
			tree[v].push_back(u);
		}
		vector<int> embedding = AG.embed(tree);
		cout << "[Test #" << _tc_num << "]: ";
		bool ok = true;
		for(auto [u, v]: tree_edge){
			u = embedding[u];
			v = embedding[v];
			if(u > v){
				swap(u, v);
			}
			if(!binary_search(edge.begin(), edge.end(), array<int, 2>{u, v})){
				ok = false;
				break;
			}
		}
		if(ok){
			cout << "OK.\n" << endl;
		}
		else{
			cout << "Embedding Failed.\n\n";
			cout << "<Admissible Graph Edges>\n";
			for(auto [u, v]: edge){
				cout << "{" << u << ", " << v << "}\n";
			}
			cout << "\n";
			cout << "<Tree Edges>\n";
			for(auto [u, v]: tree_edge){
				cout << "{" << u << ", " << v << "}\n";
			}
			cout << "\n";
			return 0;
		}
	}
	return 0;
}