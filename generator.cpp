#include <iostream>
#include <vector>
#include <random>
#include <cstdlib>
#include <cmath>

using namespace std;

int main(int argc, char* argv[]) {
    // team, rounds, winning probability, bias of team 1
    int n = (argc > 1) ? atoi(argv[1]) : 512;
    int c = (argc > 2) ? atoi(argv[2]) : 100;
    double alpha = (argc > 3) ? atof(argv[3]) : 0.5;
    double beta = (argc > 4) ? atof(argv[4]) : 0.1;

    if (n <= 0 || c <= 0  || alpha < 0.0 || alpha > 1.0 || beta < -1.0 || beta > 1.0) {
        cerr << "Invalid arguments. Ensure n > 0, c > 0, and 0 ≤ alpha ≤ 1, and -1 ≤ beta ≤ 1.\n";
        return 1;
    }

    vector<vector<int>> G(n, vector<int>(n, c));
    vector<vector<double>> p(n, vector<double>(n, 0.0));
    vector<int> w(n, 0);

    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<> dist(0.0, 1.0);

    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j)
            p[i][j] = min(1.0, dist(gen) + (i == 0 ? beta : 0.0));

    int N = c * (n * (n - 1)) / 2;
    int samples = static_cast<int>(ceil(alpha * N));
    uniform_int_distribution<> dist_i(0, n - 2);
    uniform_int_distribution<> dist_j(1, n - 1);

    while (samples--) {
        int i, j;
        do {
            i = dist_i(gen);
            j = dist_j(gen);
        } while (i >= j || G[i][j] == 0);

        int k = (dist(gen) < p[i][j]) ? i : j;

        G[i][j] -= 1;
        w[k] += 1;
    }

    cout << n << endl;
    for(auto e : w)
        cout << e << " ";
    cout << endl;

    for (int i = 0; i + 1 < n; ++i) {
        for (int j = i + 1; j < n; ++j)
            cout << G[i][j] << " ";
        cout << endl;
    }

    return 0;
}
