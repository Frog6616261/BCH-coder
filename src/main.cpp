#include <iostream>
#include <vector>
#include <set>
#include <tuple>
#include <cmath>
#include <bitset>
#include <random>
#include <algorithm>
#include <numeric>
#include <functional>


#define vect_b std::vector<bool>
#define vect_int std::vector<int>
#define vect_vect_int std::vector<std::vector<int>>
#define vect_vect_b std::vector<std::vector<bool>>


template<typename T>
inline std::vector<T> read_vector(int size) {
    std::vector<T> result(size);
    for (int i = 0; i < size; i++) {
        T word;
        std::cin >> word;
        result[i] = word;
    }

    return result;
}

class BCH{
private:

//params BCH
//int t_; //max count of errors
int d_;
int b_ = 1; //since the binary code in the narrow sense
int k_;
int r_; //max degrees of code-generation polinom
int n_; //size of code, n = q^m - 1
//int vs_; //size polinom vector
int fs_; //size of galua field
int p_; //primitive polinom, x - primitive element this polinom p(x)

vect_int g_; //generate polinom
vect_int gen_pol_; //the generate polinom, that generating a ring of polynomials


vect_int F_ptd_; // Galua Field(fs_ = p^m)
vect_int F_dtp_; // pow by decimal
vect_vect_int M_pptd_; // Table of multiplie in GF(fs_ = p^m). pol * pol = dec
vect_vect_int M_ddtd_; // Table of multiplie in GF(fs_ = p^m). dec * dec = dec


void create_generate_polinom(){
    //generate cyclotomic classes
    std::vector<std::set<int>> cycl_clases;
    std::set<int> bases_of_cycl_clases;
    std::set<int> pow_num;
    for (int i = b_; i < n_; i++) pow_num.insert(i);
    
    int cur_base_pow;
    int cur_pow;
    for (int i = b_; i < n_; i++){
        if (pow_num.empty()) break;

        //find base of cyclotomic class
        std::set<int> cur_clas;
        cur_base_pow = *pow_num.begin();
        cur_pow = cur_base_pow;
        bases_of_cycl_clases.insert(cur_base_pow);

        for (int j = b_; j < n_; j++){

            cur_clas.insert(cur_pow);
            pow_num.erase(cur_pow);
            cur_pow = (cur_pow * 2) % n_;

            if (cur_pow == cur_base_pow) break;             
        }

        cycl_clases.push_back(cur_clas);
    }

    //multiplie linear polinoms
    g_ = std::vector<int>(1, 1);
    int size_g = 1;
    int clas_num = 0;
    r_ = 0;
    
    for (int base_of_clas: bases_of_cycl_clases){
        if (base_of_clas > (d_ - 2)) break;

        for (int cur_deg: cycl_clases[clas_num]){
            //resize polinom g(x) * x
            g_.push_back(1);            
            size_g++;
            for (int i = (size_g - 2); i >= 1; i-- ) g_[i] = g_[(i - 1)]; 
            g_[0] = 0;

            //sum g(x)*x + a^i * g(x)
            for (int i = 0; i < (size_g - 1); i++ ) g_[i] ^= M_ddtd_[F_ptd_[cur_deg]][g_[i + 1]]; 
            r_++;
        }

        clas_num++;
    }

    //find k
    k_ = n_ - r_;
}

void fill_Galua_field(){
    fs_ = n_ + 1;
    // fille the GF by deg of primitive element and primitive polinom
    F_ptd_ = std::vector<int>(fs_, -1);  // transfor pow to dec    
    F_dtp_ = std::vector<int>(fs_, -1); // transform dec to pow    
    
    int a = 1;
    for (int i = 1; i < fs_; i++){
        a <<= 1;
        if (a >= fs_) a = a^p_;
        F_ptd_[i] = a;
        F_dtp_[a] = i;
    }

    F_ptd_[0]  = 1;
    F_dtp_[1] = 0; 

    //fill multiplie table (pow element mult pow element = dec element) 
    M_pptd_ = std::vector<std::vector<int>>(n_, std::vector<int>(n_, 0));

    for (int row = 0; row < n_; row++){
        for (int col = 0; col <= row; col++){
            M_pptd_[row][col] = F_ptd_[(row + col) % n_];
            if (row == col) continue;
            M_pptd_[col][row] = M_pptd_[row][col];
        }
    }

    //fill multiplie table (dec element mult dec element = dec element) 
    M_ddtd_ = std::vector<std::vector<int>>(fs_, std::vector<int>(fs_, 0));

    for (int row = 1; row < fs_; row++){
        for (int col = 1; col <= row; col++){
            M_ddtd_[row][col] = M_pptd_[F_dtp_[row]][F_dtp_[col]];
            if (row == col) continue;
            M_ddtd_[col][row] = M_ddtd_[row][col];
        }
    }

    //create ring-generation polinom
    gen_pol_ = std::vector<int>(fs_, 0);
    gen_pol_[0] = 1;
    gen_pol_[n_] = 1;
}


public:

BCH(int n, int a_dec, int d){
    n_ = n;
    d_ = d;
    p_ = a_dec;

    fill_Galua_field();
    create_generate_polinom();
}

vect_b encode(std::vector<bool>& word_in){
    if (word_in.size() != k_) return vect_b();

    //create infom vector with degree n_ - k_ = r_
    vect_b result(n_, false);

    //fill n - k = r to n - 1
    for (size_t i = r_; i < n_ ; i++) result[i] = word_in[i - r_];

    //find rest i(x) mod g(x)
    std::vector<bool> rest = result;

    for (int i = n_ - 1; i >= r_; --i){
        if (rest[i]){
            int num = 0;
            for (int j = r_; j >= 0; j--){
                rest[i - num] = rest[i - num]^(g_[j] == 1);
                num++;
            } 
        }
    }

    for (size_t i = 0; i < r_; i++){
        result[i] = rest[i];
    } 


    return result;
}

void decode(std::vector<bool>& word_in){ 

    //create Sindrome value vector polinom
    vect_int S((d_ - 1), 0);
    int count_not_zero_S = 0;

    for (int deg_prim = 0; deg_prim < d_ - 1; deg_prim++){
        int cur_S_val = 0;

        for (int deg_word_in = 0; deg_word_in < n_; deg_word_in++){
            if (word_in[deg_word_in]){
            cur_S_val ^= F_ptd_[((deg_prim + b_) * deg_word_in) % n_];
            }
        }
        
        if (cur_S_val != 0) count_not_zero_S++;
        S[deg_prim] = cur_S_val;
    }

    //doesn't have errors
    if (count_not_zero_S == 0) return;

    //Berlekamp–Massey algorithm
    //register length
    size_t L = 0;
    size_t m = 0;

    //create locators polinom
    vect_int A(1, 1);

    //create discrepancy compensating polynomial
    vect_int B(1, 1);
    
    for (size_t r = 1; r <= (d_ - 1); ++r){

        size_t D = 0; //discrepancy
        size_t size_A = A.size();

        for (int j = 0; j <= std::min(L, size_A); j++) D ^= M_ddtd_[A[j]][S[r - j - 1]];
        
        if (D == 0) continue;
        
        size_t size_B = B.size();            
        vect_int T = A;
        T.resize(std::max(size_A, (r - m + size_B)), 0);

        for (size_t i = 0; i < size_B; ++i) T[r - m + i] ^= M_ddtd_[D][B[i]];

        while (T.size() > 1 && T.back() == 0) T.pop_back();
            
        if ((2 * L) <= (r - 1)){
            //B.clear();
            B.resize(size_A, 0);
            size_t D_inv = F_ptd_[((n_ - F_dtp_[D]) % n_)];

            for (size_t i = 0; i < B.size(); ++i){
                if (A[i] != 0) B[i] = M_ddtd_[D_inv][A[i]];
            } 

            L = r - L;
            m = r;
        }

        A = T;        
    }

    //too many errors
    size_t size_A = A.size();
    if ((size_A - 1) != L) return;

    // locate error positions
    vect_int errors;
    // if lambda(a^-x) = 0, there is an error in position x
    for (size_t i = 0; i < n_; ++i) {
        size_t res = A[0];
        
        for (size_t l = 1; l < size_A; ++l){
            size_t mul = M_ddtd_[A[l]][F_ptd_[(i * l) % n_]];
            res ^= mul;
        } 

        if (res == 0) {
            size_t pow_inw = (n_ - i) % n_;
            errors.push_back(pow_inw);
            word_in[pow_inw] = !word_in[pow_inw];
            if (errors.size() == L) break;
        }
    }
}

template<typename T>
inline void print_poly(std::vector<T>& poly, int size){
    if (size > poly.size()){
        std::cout << "not correct" <<std::endl;
        return;
    } 

    for (int i = 0; i < size; i++) std::cout<< poly[i]<< " ";
    std::cout<<std::endl;
}

void print_code_gener_polinom(){
    print_poly(g_, (r_ + 1));
}

void print_k(){
    std::cout<< k_ <<std::endl;
}

int get_k_(){
    return k_;
}

};



int main(int argc, char* kwarg[]){

    //read data
    std::freopen("input.txt", "r", stdin);
    std::freopen("output.txt", "w", stdout);

    int n, a, d;
    std::cin>>n;
    std::cin>>a;
    std::cin>>d;

    //create BCH object
    BCH code{n, a, d};

    //print paarametrs of code
    code.print_k();
    code.print_code_gener_polinom();
    int k = code.get_k_();


    //parametrs for Simulate
    std::random_device rand{};
    std::mt19937 gen{rand()};
    auto gen_bit = std::bind(std::uniform_int_distribution<>(0, 1), std::default_random_engine());
    std::uniform_real_distribution<> dist(0, 1);

    //do the command
    std::string command;
    while(std::cin>>command){
        if (command == "Encode"){
            std::vector<bool> word_in = read_vector<bool>(k);
            std::vector<bool> word_out(n, false);
            word_out = code.encode(word_in);
            for (bool i : word_out) std::cout << i << " ";
            std::cout << std::endl;
        }

        if (command == "Decode"){
            std::vector<bool> word_in = read_vector<bool>(n);
            code.decode(word_in);
            for (bool i : word_in) std::cout << i << " ";
            std::cout << std::endl;
        } 

        if (command == "Simulate"){
            double snrb;
            int numb_of_simulations, max_error;
            std::cin >> snrb >> numb_of_simulations >> max_error;

            int errs = 0;
            int iters = 0;
            std::vector<bool> word_in(k);
            std::vector<bool> word_in_ch(n);
            std::vector<bool> word_out_ch(n);

            for (int i = 0; i < numb_of_simulations && errs < max_error; ++i){
                iters++;

                for (int j = 0; j < k; j++) word_in[j] = gen_bit();
                word_in_ch = code.encode(word_in);
                
                //generete out vector               
                for (int t = 0; t < n; t++) word_out_ch[t] = (dist(gen) <= snrb) ? !word_in_ch[t] : word_in_ch[t];
                code.decode(word_out_ch);

                if (word_in_ch != word_out_ch) ++errs;
            }
            std::cout << std::uppercase << std::scientific << (double) errs / iters << std::endl;
        } 
    }

    return 0;
}