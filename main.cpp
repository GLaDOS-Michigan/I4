#include<cstdio>
#include<cstring>
#include<map>
#include<set>
#include<string>
#include<algorithm>
#include<vector>

//#define DEBUG

using std::make_pair;
using std::pair;
using std::string;
using std::map;
using std::vector;
using std::set;
using std::to_string;
map<string, int> var_to_id;
map<string, vector< pair<string, int> > > const_types;

const int sizeN = 10000;
const int N1 = 1000;
const int N3 = 1000;
int n = 0, n1, n2, n3;
int len[sizeN];
int try_level[sizeN];
int arg[sizeN];
char relation[sizeN][1000];
char arg_type[N3][100][100];

char invs[sizeN][1000];
string results[sizeN], prefix[sizeN];
set<pair<string, int> > vars[sizeN];
int max_level;

char type[10000][10000], var[10000][10000], specifies[N1][100][100];
char t[10000], name[10000];

int value;
string model_name;
string inv_prefix;

struct comp{
    bool operator()(const vector<int> &a, const vector<int> &b) const {
        if (a.size() < b.size()) return true;
        if (a.size() > b.size()) return false;
        for (int i = 0; i < a.size(); i++) {
            fprintf(stderr, "comp: %d %d\n", a[i], b[i]);
            if (a[i] < b[i]) return true;
            if (a[i] > b[i]) return false;
        }
        return false;
    }
};

set<vector<int>> rela[1000];

void read_invariants(FILE *fi) {
    while (fgets(invs[n++], 1000, fi)) {
        int l = 0;
        for (int i = 0; invs[n-1][i]; i++) 
            if (invs[n-1][i] != '\\') {
                if (invs[n-1][i] != '\t' && invs[n-1][i] != '&' && invs[n-1][i] != '\n')
                    if (invs[n-1][i] == '\'') {
                        while (invs[n-1][l - 1] != ' ') l--;
                        i++;
                    } else invs[n-1][l++] = invs[n-1][i];
        }
        invs[n-1][l] = 0;
        if (!l || invs[n-1][0] == '[' || (invs[n-1][0] == '(' && invs[n-1][3] == ':') || invs[n-1][0] == 'p') n--;

    }
    n--;
}

void read_config(FILE *config) {
    fscanf(config, "%d\n", &n1);
    for (int i = 0; i < n1; i++) {
        fscanf(config, "%d %s %s", &len[i], type[i], var[i]);
        var_to_id[string(var[i])] = i;
        for (int j = 0; j < len[i]; j++)
            fscanf(config, "%s", specifies[i][j]);
        fscanf(config, "\n");
    }
    fscanf(config, "%d\n", &n2);
    for (int i = 0; i < n2; i++) {
        fscanf(config, "%s %s = %d", t, name, &value);
        const_types[string(t)].push_back(make_pair(string(name), value));
    }
    fscanf(config, "%d\n", &n3);
    max_level = 1<<(n2 + n3);
    for (int i = 0; i < n3; i++) {
        fscanf(config, "%d %s", &arg[i], relation[i]);
        for (int j = 0; j < arg[i]; j++) {
            fscanf(config, "%s", arg_type[i][j]);
        }
        int j;
        fscanf(config, "%d", &j);
        while (j--) {
            vector<int> vec;
            int x;
            for (int k = 0; k < arg[i]; k++) {
                fscanf(config, "%d", &x);
                vec.push_back(x);
            }
            rela[i].insert(vec);
        }
    }
}

void print() {
    FILE *ivy = fopen((model_name + ".ivy").c_str(), "r");
    FILE *out = fopen((model_name + "_inv.ivy").c_str(), "w");
    char st[100000];
    while (fgets(st, 100000, ivy)) fprintf(out, "%s", st);
    fputs("", out);
    for (int i = 0; i < n; i++) {
        if (prefix[i].length()){
            fprintf(out, "invariant [%d] (%s) -> (%s)\n", i, prefix[i].c_str(), results[i].c_str());
        } else {
            fprintf(out, "invariant [%d] %s\n", i, results[i].c_str());
        }
    }
    fclose(ivy);
    fclose(out);
}

void check_input() {
    for (int i = 0; i < n; i++) printf("%s\n", invs[i]);
    puts("");
    for (auto it = var_to_id.begin(); it != var_to_id.end(); it++) {
        printf("%s:", it->first.c_str());
        for (int i = 0; i < len[it->second]; i++) printf(" %s", specifies[it->second][i]);
        puts("");
    }
    puts("");
    for (auto it = const_types.begin(); it != const_types.end(); it++) 
        for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
        printf("%s %s = %d\n", it->first.c_str(), it2->first.c_str(), it2->second);
    }
    puts("");
    for (int i = 0; i < n3; i++) {
        printf("%s(%s", relation[i], arg_type[i][0]);
        for (int j = 1; j < arg[i]; j++) printf(", %s", arg_type[i][j]);
        puts(")");
        for (auto &it : rela[i]) {
            for (auto &j : it) printf("%d ", j);
            puts("");
        }
        puts("");
    }
    puts("done");
}

string get_constant(string var, int value, set<pair<string, int> > &vars) {
#ifdef DEBUG
    printf("variable: %s value: %d\n", var.c_str(), value);
#endif
    // string t = type[var_to_id[var]];
    // for (auto it = const_types[t].begin(); it != const_types[t].end(); it++) {
    //     if (it->second == value) return it->first;
    // }
    // fprintf(stderr, "???");
    // throw "?";
    // return "!!!!!!!!!!";
    pair<string, int> variable = make_pair(var, value);
    vars.insert(variable);
    return var + std::to_string(value);
}

string translate(char *st, set<pair<string, int> > &vars) {
    char *pos = strchr(st, '_');
    if (pos) {
        while (pos[1] < '0' || pos[1] > '9') {
            pos = strchr(pos + 1, '_');
            if (!pos) return st;
        }
        *pos = 0;
        string result(st);
        int id = var_to_id[result];
        for (int i = 0; i < len[id]; i++) {
            pos++;
            char *next = strchr(pos, '_');
            if (next) *next = 0;
            if (i != 0) result += ", " + get_constant(string(specifies[id][i]), atoi(pos), vars);
            else result += "(" + get_constant(string(specifies[id][i]), atoi(pos), vars);
            pos = next;
        }
        result += ")";
        return result;
    } else {
        string type = "";
        for (; *st < '0' || *st > '9'; st++)
            type += string(1, *st);
        int val = atoi(st);
        vars.insert(make_pair(type, val));
        return type + std::to_string(val);
    }
}

bool check(vector<int> &vec, set<vector<int> > &rela) {
    int i;
    for (auto &it : rela) {
        for (i = 0; i < vec.size(); i++) {
            if (vec[i] != it[i]) break;
        }
        if (i == vec.size()) {
            // for (auto i : it) printf("%d ", i);
            // puts("");
            // for (int i = 0; i < vec.size(); i++) printf("%d ", vec[i]);
            // puts("");
            return true;
        }
    }
    return false;
}


string search(int x, int i, vector<int> vec, const set<pair<string, int> > &vars) {
    if (x == arg[i]) {
        if (check(vec, rela[i])) {
            string st = string(relation[i]) + "(" +arg_type[i][0] + to_string(vec[0]);
            for (int j = 1; j < arg[i]; j++)
                st += string(", ") + arg_type[i][j] + to_string(vec[j]);
            st += ") & ";
            return st;
        } else return "";
    }
    string st;
    for (auto it = vars.begin(); it != vars.end(); it++) {
        if (it->first == string(arg_type[i][x])) {
            vec.push_back(it->second);
            st += search(x + 1, i, vec, vars);
            vec.pop_back();
        }
    }
    return st;
}

void refine(int x) {
    try_level[x] = try_level[x] * 2 + 1;
    if (try_level[x] < 0) try_level[x] = 0;
    if (try_level[x] >= max_level)
    {
//        printf("No refinement for %d!\n", x);
        prefix[x] = "false";
        return;
    }
    string st;
/*    if (try_level[x]) {
        for (auto it1 = vars[x].begin(); it1 != vars[x].end(); it1++)
            for (auto it2 = it1; it2 != vars[x].end(); it2++) {
                    if (it1->first == it2->first && it1->first == "EPOCH") {
                        if (it1->second < it2->second) {
                            st += "le(" + it1->first + std::to_string(it1->second) + ", " + it2->first + std::to_string(it2->second) + ") & ";
                        } else if (it1->second > it2->second) {
                            st += "le(" + it2->first + std::to_string(it2->second) + ", " + it1->first + std::to_string(it1->second) + ") & ";
                        }
                    }
            }
    }*/
    auto it1 = const_types.begin();
    auto it2 = it1->second.begin();
    int j = try_level[x];
    for (int i = 0; i < n2; i++) {
        if ((1 << i) & j) {
            for (auto & it3 : vars[x]) {
                if (it3.first == it1->first) {
                    if (it3.second == it2->second)
                        st += it3.first + std::to_string(it2->second) + " = " + it2->first + " & ";
                    else st += it3.first + std::to_string(it3.second) + " ~= " + it2->first + " & ";
                }
            }
        }
        it2++;
        if (it2 == it1->second.end()) {
            it1++;
            it2 = it1->second.begin();
        }
    }
    j = j >> n2;
    for (int i = 0; i < n2; i++) {
        if ((1 << i) & j) {
            st += search(0, i, vector<int>(), vars[x]);
        }
    }
    if (st.size()) st.replace(st.rfind(" & "), 3, "");
    prefix[x] = st;
    // printf("%s\n", st.c_str());
}

void init() {
    for (int i = 0; i < n; i++) {
        char st1[100], st2[100], *pos = invs[i];
        string result;
        while (*pos) {

#ifdef DEBUG
            printf("now: %s\n", pos);
#endif

            if (*pos == '!' || *pos == '(' || *pos == ')' || *pos == ' ') {
                if (*pos == '!') result += '~';
                else result += *pos;
                pos++;
            }
            else {
                if (sscanf(pos, "%s %s", st1, st2) != 2 || (strcmp(st2, "==") && strcmp(st2, "!=") && strcmp(st2, "<="))) {
#ifdef DEBUG
                    printf("%s %s\n", st1, st2);
#endif
                    pos += strlen(st1);
                    int cnt = 0;
                    char *tmp = st1;
                    while ((tmp = strchr(++tmp, ')'))) cnt++;
                    if (strchr(st1, ')')) *strchr(st1, ')') = 0;
                    result += translate(st1, vars[i]);
                    while (cnt--) result += ')';
                    result += " && ";
                } else {
#ifdef DEBUG
                    printf("%s %s\n", st1, st2);
#endif
                    pos += strlen(st1) + strlen(st2) + 2;
                    //printf("rest: %s\n", pos);
                    if (strcmp(st2, "==") == 0) st2[1] = 0;
                    else if (strcmp(st2, "!=") == 0) st2[0] = '~';

                    if (strcmp(st2, "<=") == 0) {
                        result += "le(" + translate(st1, vars[i]) + ", ";
                    } else {
                        result += "(" + translate(st1, vars[i]) + " " + st2 + " ";
                    }
                    char *tmp = strchr(pos, ')');
                    *tmp = ' ';
                    sscanf(pos, "%s", st2);
                    pos += strlen(st2);
                    //printf("new: %s\n", pos);
                    if (st2[0] >= '0' && st2[0] <= '9') result += get_constant(type[var_to_id[st1]], atoi(st2), vars[i]) + ")) && ";
                    else result += translate(st2, vars[i]) + ")) && ";
                }
            }
        }
        result.replace(result.rfind("&&"), 2, "");
        while (result.find("  ") != string::npos) result.replace(result.find("  "), 2, " ");
        while (result.find(") )") != string::npos) result.replace(result.find(") )"), 3, "))");
        while (result.find("&&") != string::npos) result.replace(result.find("&&"), 2, "&");

        string distinct;
        if (inv_prefix.size() == 0) {
            distinct = "";
        } else {
            distinct = inv_prefix;
        }
        for (auto it1 = vars[i].begin(); it1 != vars[i].end(); it1++) {
            for (auto it2 = it1; it2 != vars[i].end(); it2++) {
                if (it1->first == it2->first && it1->second != it2->second) {
                    distinct += it1->first + std::to_string(it1->second) + " ~= " + it2->first + std::to_string(it2->second) + " & ";
                }
            }
        }
        if (distinct.length()) {
            distinct.replace(distinct.rfind(" & "), 3, "");
            results[i] = "(" + distinct + ") -> " + result;
        }
        else results[i] = result;
        try_level[i] = max_level / 2 - 1; refine(i);
    }
}

bool v[100000];
bool verify() {
    system(("ivy_check " + model_name + "_inv.ivy > log.txt").c_str());
    FILE *in = fopen("log.txt", "r");
    char st[100000];
    int line, id;
    bool flag = false;
    bool succeed = false;
    char str[100000];
    memset(v, 0, sizeof(v));
    while (fgets(st, 100000, in)) {
        if (strstr(st, "FAIL")) {
            sscanf(st, "%s line %d: %d", str, &line, &id);
            //printf("%s line %d: %d\n", str, line, id);
            if (id == 1000000) {
                fprintf(stderr, "failed!\n");
                exit(-1);
            }
            if (!v[id]) {
                v[id] = true;
                refine(id);
            }
            flag = true;
        }
        if (strcmp(st, "OK\n") == 0) {
            succeed = true;
        }
    }
    fclose(in);
    if (!flag) fprintf(stderr, succeed ? "succeed!\n" : "error!\n");
    return flag;
}
int main(int argc, char *argv[]) {
    if (argc < 4) {
        fprintf(stderr, "./main model_file invariant_file config_file [invariant_prefix]\n");
        return 0;
    }
    model_name = argv[1];

    read_invariants(fopen(argv[2], "r"));
    read_config(fopen(argv[3], "r"));

    if (argc == 5) {
        inv_prefix = argv[4];
    }

    //check_input();

    init();
    int cnt = 0;
    do {
        fprintf(stderr, "\niteration %d\n", ++cnt);
        print();
    } while (verify());
    return 0;
}
