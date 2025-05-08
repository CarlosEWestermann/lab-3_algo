#include <iostream>
#include <vector>
#include <string>
#include <limits>
#include <sstream>
#include <utility>
#include <cmath>
#include <fstream>
#include <algorithm>
#include <chrono>

class k_heap {
private:
    int* heap_arr;
    int* positions;
    std::vector<long long> bottleneck;
    int capacity;
    int current_size;
    int k;

    void swap(int i, int j) {
        int temp = heap_arr[i];
        heap_arr[i] = heap_arr[j];
        heap_arr[j] = temp;
        positions[heap_arr[i]] = i;
        positions[heap_arr[j]] = j;
    }
    int parent(int i) const { return (i - 1) / k; }
    int child(int i, int j) const { return k * i + j + 1; }
    bool is_leaf(int i) { return child(i, 0) >= current_size; }
    bool root(int i) { return i == 0; }

    void heapify_up(int i) {
        if (root(i)) return;
        if (bottleneck[heap_arr[parent(i)]] < bottleneck[heap_arr[i]]) {
            swap(i, parent(i));
            heapify_up(parent(i));
        }
    }
    void heapify_down(int i) {
        if (is_leaf(i)) return;
        int largest_child = child(i, 0);
        for (int j = 1; j < k; j++) {
            int child_idx = child(i, j);
            if (child_idx < current_size && bottleneck[heap_arr[child_idx]] > bottleneck[heap_arr[largest_child]]) {
                largest_child = child_idx;
            }
        }
        if (bottleneck[heap_arr[largest_child]] > bottleneck[heap_arr[i]]) {
            swap(i, largest_child);
            heapify_down(largest_child);
        }
    }

public:
    k_heap(int cap, int k_value) {
        if (k_value < 2) throw std::invalid_argument("k must be at least 2");
        capacity = cap;
        heap_arr = new int[capacity];
        positions = new int[capacity];
        bottleneck.resize(capacity, 0);
        current_size = 0;
        k = k_value;
        for (int i = 0; i < capacity; i++) positions[i] = -1;
    }
    ~k_heap() { delete[] heap_arr; delete[] positions; }
    bool isEmpty() { return current_size == 0; }
    int size() { return current_size; }
    bool isInHeap(int vertex) { return positions[vertex] != -1; }
    long long getBottleneck(int vertex) { return bottleneck[vertex]; }
    void setBottleneck(int vertex, long long value) { bottleneck[vertex] = value; }
    int getMax() {
        if (current_size <= 0) throw std::runtime_error("Heap is empty");
        return heap_arr[0];
    }
    void insert(int vertex) {
        heap_arr[current_size] = vertex;
        positions[vertex] = current_size;
        heapify_up(current_size);
        current_size++;
    }
    void deleteKey(int i) {
        if (i >= current_size) throw std::out_of_range("Index out of range");
        int vertex_to_remove = heap_arr[i];
        heap_arr[i] = heap_arr[current_size - 1];
        positions[heap_arr[i]] = i;
        positions[vertex_to_remove] = -1;
        current_size--;
        if (i > 0 && bottleneck[heap_arr[i]] > bottleneck[heap_arr[parent(i)]]) {
            heapify_up(i);
        } else {
            heapify_down(i);
        }
    }
    void update(int vertex, long long new_value) {
        if (positions[vertex] == -1) {
            bottleneck[vertex] = new_value;
            insert(vertex);
        } else {
            long long old_value = bottleneck[vertex];
            bottleneck[vertex] = new_value;
            int i = positions[vertex];
            if (new_value > old_value) {
                heapify_up(i);
            } else if (new_value < old_value) {
                heapify_down(i);
            }
        }
    }
    
    void deleteMax() {
        if (current_size <= 0) throw std::runtime_error("Heap is empty");
        deleteKey(0);
    }
};

struct Edge {
    int from, to;
    long long capacity, flow;
    long long residual() const { return capacity - flow; }
};

struct Graph {
    int n;
    std::vector<Edge> edges;
    std::vector<std::vector<int>> adj;
    
    Graph(int num_vertices = 0) {
        n = num_vertices;
        adj.resize(num_vertices);
    }
    
    void addEdge(int u, int v, long long c) {
        int idx = edges.size();
        edges.push_back({u, v, c, 0});
        edges.push_back({v, u, 0, 0});
        
        if (u >= (int)adj.size() || v >= (int)adj.size()) {
            adj.resize(std::max(u, v) + 1);
        }
        
        adj[u].push_back(idx);
        adj[v].push_back(idx + 1);
    }
    
    void resetFlow() { 
        for (auto& edge : edges) edge.flow = 0; 
    }
};

long long fattestPath(Graph& g, int source, int sink, int k_value = 2) {
    std::vector<int> parent(g.adj.size(), -1);
    std::vector<int> edge_used(g.adj.size(), -1);
    std::vector<long long> bottleneck(g.adj.size(), 0);
    long long max_flow = 0;

    while (true) {
        std::fill(parent.begin(), parent.end(), -1);
        std::fill(bottleneck.begin(), bottleneck.end(), 0);

        k_heap heap(g.adj.size(), k_value);
        std::vector<bool> in_heap(g.adj.size(), false);

        bottleneck[source] = std::numeric_limits<long long>::max();
        heap.setBottleneck(source, bottleneck[source]);
        heap.insert(source);
        in_heap[source] = true;

        while (!heap.isEmpty() && parent[sink] == -1) {
            int u = heap.getMax();
            heap.deleteMax();
            in_heap[u] = false;

            for (int edge_idx : g.adj[u]) {
                Edge& e = g.edges[edge_idx];
                if (e.residual() > 0) {
                    long long new_bottleneck = std::min(bottleneck[u], e.residual());
                    if (new_bottleneck > bottleneck[e.to]) {
                        bottleneck[e.to] = new_bottleneck;
                        parent[e.to] = u;
                        edge_used[e.to] = edge_idx;
                        heap.setBottleneck(e.to, new_bottleneck);
                        if (!in_heap[e.to]) {
                            heap.insert(e.to);
                            in_heap[e.to] = true;
                        } else {
                            heap.update(e.to, new_bottleneck);
                        }
                    }
                }
            }
        }

        if (parent[sink] == -1) break;

        long long path_flow = bottleneck[sink];
        for (int v = sink; v != source; v = parent[v]) {
            int edge_idx = edge_used[v];
            g.edges[edge_idx].flow += path_flow;
            g.edges[edge_idx ^ 1].flow -= path_flow;
        }
        max_flow += path_flow;
    }
    return max_flow;
}

bool canTeam1Win(const std::vector<int>& wins, const std::vector<std::vector<int>>& gamesRemaining) {
    int n = wins.size();
    //1) a equipe 1 vence todos os seus r1 jogos restantes, portanto, tem w1 + r1 vitórias
    int team1FinalWins = wins[0];
    for (int j = 1; j < n; j++) {
        team1FinalWins += gamesRemaining[0][j];
    }
    
    //ii) todas as outras equipes i ∈ T = [2, n] vencem no máximo mi jogos, dado por wi + mi < w1 + r1 i.e. mi = w1 + r1 − wi − 1 
    std::vector<int> maxAllowedWins(n);
    for (int i = 1; i < n; i++) {
        maxAllowedWins[i] = team1FinalWins - wins[i] - 1;

        //Caso algum mi < 0 a equipe 1 já não pode ganhar mais.
        if (maxAllowedWins[i] < 0) {
            return false;
        }
    }

    
    int totalRemainingGames = 0;
    for (int i = 1; i < n; i++) {
        for (int j = i+1; j < n; j++) {
            totalRemainingGames += gamesRemaining[i][j];
        }
    }
    
    int numGameNodes = 0;
    for (int i = 1; i < n; i++) {
        for (int j = i+1; j < n; j++) {
            if (gamesRemaining[i][j] > 0) {
                numGameNodes++;
            }
        }
    }
    
    int totalNodes = 1 + n + numGameNodes + 1; 

    /*Cria um grafo com vértices  e com os seguintes arcos*/

    Graph g(totalNodes);
    
    int source = 0;
    int sink = n; 
    int gameNodeIdx = n + 1;
    
    for (int i = 1; i < n; i++) {
        for (int j = i+1; j < n; j++) {
            if (gamesRemaining[i][j] > 0) {
                //(s, g) para todo g = (i, j) ∈ G de capacidade gij,
                g.addEdge(source, gameNodeIdx, gamesRemaining[i][j]);
                //(g, i) e (g, j) para todo g = (i, j) ∈ G de capacidade ∞,
                g.addEdge(gameNodeIdx, i, std::numeric_limits<long long>::max());
                g.addEdge(gameNodeIdx, j, std::numeric_limits<long long>::max());
                
                gameNodeIdx++;
            }
        }
    }
    
    for (int i = 1; i < n; i++) {
        //(i, t) para todo i ∈ T de capacidade mi.
        g.addEdge(i, sink, maxAllowedWins[i]);
    }
    
    long long maxFlow = fattestPath(g, source, sink, 2);
    
    //Equipe 1 ainda pode vencer sse o grafo acima possui um fluxo st que satura
    return maxFlow == totalRemainingGames;
}

int main() {
    int n;
    std::cin >> n;
    
    std::vector<int> wins(n);
    for (int i = 0; i < n; i++) {
        std::cin >> wins[i];
    }

    std::vector<std::vector<int>> gamesRemaining(n, std::vector<int>(n, 0));
    
    for (int i = 0; i < n-1; i++) {
        for (int j = i+1; j < n; j++) {
            std::cin >> gamesRemaining[i][j];
            gamesRemaining[j][i] = gamesRemaining[i][j];
        }
    }
    
    bool canWin = canTeam1Win(wins, gamesRemaining);
    
    if (canWin) {
        std::cout << "sim" << std::endl;
    } else {
        std::cout << "nao" << std::endl;
    }
    
    
    return 0;
}
