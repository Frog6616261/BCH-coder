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

const int SIZE_BITS = 32;


vect_int get_gf_vect_by_dec(int pol_dec, int size_vect){
    std::vector<int> bits(size_vect, 0); 

    for (int i = 0; i < size_vect; i++) {
        bits[i] = pol_dec % 2; 
        pol_dec /= 2;         
    }

    return bits;
}


vect_int sum_vect_to_vect_in_gf(std::vector<int>& a_dec, std::vector<int>& b_dec,
 std::vector<std::vector<int>>& sum_tab){
    int size = a_dec.size();
    if (size != b_dec.size()) return std::vector<int>();

    std::vector<int> result_dec(size, -1);
    for(int i = 0; i < size; i++) result_dec[i] = sum_tab[a_dec[i]][b_dec[i]];
    return result_dec;
}


vect_int mult_vect_to_coef_in_gf(std::vector<int>& a_dec, int coef_dec,
 std::vector<std::vector<int>>& mul_table_decdec_to_dec){
    int size = a_dec.size();
    std::vector<int> result_dec(size, -1);
    for(int i = 0; i < size; i++) result_dec[i] = mul_table_decdec_to_dec[coef_dec][a_dec[i]];
    return result_dec;
}


vect_int mult_vect_to_one_element_vect_in_gf_sum_deg_less_deg_pol(std::vector<int>& a_dec, int deg_vect,
 int coef_vect, std::vector<std::vector<int>>& mul_table_decdec_to_dec){
    int size = a_dec.size();
    std::vector<int> add_vect(size, 0);

    for (int i = (size - 1); i >= deg_vect; i--)
        add_vect[i] = a_dec[i - deg_vect];    

    return mult_vect_to_coef_in_gf(add_vect, coef_vect, mul_table_decdec_to_dec);
}


vect_int rest_vect_into_vect_in_gf(std::vector<int>& a_dec, std::vector<int>& b_dec,
 std::vector<std::vector<int>>& mul_table_decdec_to_dec, std::vector<std::vector<int>>& sum_tab_decdec_to_dec,
  std::vector<int>& dec_to_pow, std::vector<int>& pow_to_dec){
    int size = a_dec.size(); //divided
    if (size != b_dec.size()) return std::vector<int>();

    std::vector<int> d{a_dec}; //divided
    std::vector<int> r{b_dec}; //divisor

    int r_deg = 0;
    int r_coef = 0;
    int d_deg = 0;
    int d_coef = 0;
    for (int i = (size - 1); i >= 0; i--){
        if (r[i] != 0){
            r_coef = r[i] ;
            r_deg = i;
            break;
        }
    }
    for (int i = (size - 1); i >= 0; i--){
        if (d[i] != 0){
            d_coef = d[i] ;
            d_deg = i;
            break;
        }
    }

    int order = pow_to_dec.size() - 1; //the order of galuafield's primitive element
    int steps = d_deg - r_deg + 1;


    std::vector<int> inter{d};
    int cur_pol_coef = 0;
    int cur_deg = 0;
    int r_pol_coef = dec_to_pow[r_coef];
    int cur_add = 0;
    for (int i = 0; i < steps; i++){
        std::vector<int> sub(size, -1);

        for (int j = (size - 1); j >= 0; j--){
            if (inter[j] != 0){
                cur_pol_coef = dec_to_pow[inter[j]] ;
                cur_deg = j;
                break;
            }
        }

        if (cur_deg < r_deg) break;

        //add number
        if (cur_pol_coef < r_pol_coef)
            cur_add = pow_to_dec[order + (cur_pol_coef - r_pol_coef)];
        else
            cur_add = pow_to_dec[(cur_pol_coef - r_pol_coef)];

        //solve subtract
        sub = mult_vect_to_one_element_vect_in_gf_sum_deg_less_deg_pol(r, (cur_deg - r_deg), cur_add, mul_table_decdec_to_dec);

        //inter = inter - sub
        inter = sum_vect_to_vect_in_gf(inter, sub, sum_tab_decdec_to_dec);            
    }

    return inter;
 
}


vect_int mult_vect_to_one_element_vect_in_gf(vect_int& a_dec, int deg_vect, int coef_vect,
 std::vector<std::vector<int>>& mul_table_decdec_to_dec, std::vector<std::vector<int>>& sum_table_decdec_to_dec,
 vect_int& dec_to_pow, vect_int& pow_to_dec,
 vect_int& generate, int deg_gen ){
    int size = a_dec.size();
    int a_deg = 0;
    if (size != (deg_gen + 1)) return std::vector<int>();

    for (int i = (size - 1); i >= 0; i--){
        if (a_dec[i] != 0){
            a_deg = i;
            break;
        } 
    }      
    
    if ((a_deg + deg_vect) < deg_gen){
        return mult_vect_to_one_element_vect_in_gf_sum_deg_less_deg_pol(a_dec, deg_vect, coef_vect, mul_table_decdec_to_dec);
    }

    // size of expanded vector
    int size_ex = a_deg + deg_vect + 1;

    //create expanded polinoms for find rest
    std::vector<int> generate_ex(size_ex, 0); 
    std::vector<int> a_ex(size_ex, 0);

    for (int i = 0; i <= deg_gen; i++){
        generate_ex[i] = generate[i];
        if (i <= a_deg) a_ex[i] = a_dec[i];
    }

    //create result vector
    std::vector<int> add_result(size_ex, -1);
    std::vector<int> result(size, -1);

    add_result = mult_vect_to_one_element_vect_in_gf_sum_deg_less_deg_pol(a_ex, deg_vect, coef_vect, mul_table_decdec_to_dec);

    add_result = rest_vect_into_vect_in_gf(add_result, generate_ex, mul_table_decdec_to_dec, sum_table_decdec_to_dec, dec_to_pow, pow_to_dec);
    
    for (int i = 0; i < size; i++) result[i] = add_result[i];

    return result;
}


vect_int mult_vect_to_vect_in_gf(vect_int& a, vect_int& b,
std::vector<std::vector<int>>& mul_table_decdec_to_dec, std::vector<std::vector<int>>& sum_table_decdec_to_dec,
vect_int& pow_to_dec, vect_int& dec_to_pow, vect_int& generate, int deg_generate){
    int size = a.size();
    if (size != b.size() || generate.size() != (deg_generate + 1)) return std::vector<int>();

    std::vector<int> inter(size, 0);
    std::vector<int> additional(size, 0);

    for(int i = 0; i < size; i++){
        if (b[i] == 0) continue;

        additional = mult_vect_to_one_element_vect_in_gf(a, i, b[i], mul_table_decdec_to_dec, sum_table_decdec_to_dec,
         dec_to_pow, pow_to_dec, generate, deg_generate);
        inter = sum_vect_to_vect_in_gf(inter, additional, sum_table_decdec_to_dec);
    } 

    return inter;
}


int solve_poly_by_coef_in_gf(vect_int& a, int coef_dec,
std::vector<std::vector<int>>& mul_table_decdec_to_dec, std::vector<std::vector<int>>& sum_table_decdec_to_dec,
vect_int& pow_to_dec, vect_int& dec_to_pow, int deg_generate){

    int res = a[0];
    if (coef_dec == 0) return 0;

    for (int deg_a = 1; deg_a < deg_generate; deg_a++){
        if (a[deg_a] == 0) continue;

        int cur_coef_in_deg = pow_to_dec[(dec_to_pow[coef_dec] * deg_a) % deg_generate];
        int cur_coef = mul_table_decdec_to_dec[cur_coef_in_deg][a[deg_a]];
        res = sum_table_decdec_to_dec[res][cur_coef];
    }

    return res;
}

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
vect_vect_int S_ddtd_; // Table of sum in GF(fs_ = p^m). dec + dec = dec


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
        
        // //fill the current cyclotomic class
        // do {            
        //     cur_clas.insert(cur_pow);
        //     pow_num.erase(cur_pow);  
        //     cur_pow = (cur_pow * 2) % n_;
        // }while(cur_pow != cur_base_pow);

        cycl_clases.push_back(cur_clas);
    }

    // //multiplie linear polinoms
    // g_ = std::vector<int>(fs_, 0);
    // g_[0] = F_ptd_[0];
    // int clas_num = 0;
    // r_ = 0;
    // std::vector<int> inter(fs_, 0);
    
    // for (int base_of_clas: bases_of_cycl_clases){
    //     if (base_of_clas > (d_ - 2)) break;

    //     int count = cycl_clases[clas_num].size();
    //     for (int cur_deg: cycl_clases[clas_num]){
    //         //create (x - a^{cur_deg})
    //         inter[0] = F_ptd_[cur_deg];
    //         inter[1] = F_ptd_[0];

    //         g_ = mult_vect_to_vect_in_gf(g_, inter, M_ddtd_, S_ddtd_, F_ptd_, F_dtp_, gen_pol_, n_);
    //         r_++;
    //     }

    //     clas_num++;
    // }

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
            for (int i = 0; i < (size_g - 1); i++ ) g_[i] = S_ddtd_[M_ddtd_[F_ptd_[cur_deg]][g_[i + 1]]][g_[i]]; 
            r_++;
        }

        clas_num++;
    }
    
    // //resize g_ for correct decode
    // g_.resize(fs_, 0);

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

    //fill sum table 
    S_ddtd_ = std::vector<std::vector<int>>(fs_, std::vector<int>(fs_, 0));

    for (int row = 0; row < fs_; row++){
        for (int col = 0; col < row; col++){
            S_ddtd_[row][col] = row^col;
            S_ddtd_[col][row] = S_ddtd_[row][col];
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

    // //create infom vector with degree n_ - k_ = r_
    // std::vector<int> temp(fs_, 0);
    // for (int i = (n_ - 1); i >= r_; i--) temp[i] = word_in[i - r_];

    // //find rest for code word
    // std::vector<int> rest(fs_, 0);
    // rest = rest_vect_into_vect_in_gf(temp, g_, M_ddtd_, S_ddtd_, F_dtp_, F_ptd_);    
    // temp = sum_vect_to_vect_in_gf(temp, rest, S_ddtd_);

    // //create result
    // vect_b res(n_, false);
    // for (int i = 0; i < n_; i++){
    //     res[i] = static_cast<bool>(temp[i]);
    //     //if (temp[i] != 0 && temp[i] != 1) return vect_b();
    // }

    //create infom vector with degree n_ - k_ = r_
    vect_b result(n_, false);

    //fill n - k = r to n - 1
    for (int i = r_; i < n_ ; i++) result[i] = word_in[i - r_];

    //find rest i(x) mod g(x)
    std::vector<bool> rest = result;

    for (int i = n_ - 1; i >= r_; --i){
        if (rest[i]){
            int num = 0;
            for (int j = r_; j >= 0; j--){
                rest[i - num] = rest[i - num]^static_cast<bool>(g_[j]);
                num++;
            } 
        }
    }

    for (int i = r_ - 1; i >= 0; i--){
        result[i] = rest[i];
    } 


    return result;
}

void decode_long_time(std::vector<bool>& word_in){

    //create Sindrome value vector polinom
    vect_int S{};
    int count_not_zero_S = 0;

    for (int deg_prim = 0; deg_prim < d_ - 1; deg_prim++){
        int cur_S_val = 0;

        for (int deg_word_in = 0; deg_word_in < n_; deg_word_in++){
            if (!word_in[deg_word_in]) continue;
            cur_S_val = S_ddtd_[cur_S_val][F_ptd_[((deg_prim + b_) * deg_word_in) % n_]];
        }
        
        if (cur_S_val != 0) count_not_zero_S++;
        S.push_back(cur_S_val);
    }

    //doesn't have errors
    if (count_not_zero_S == 0) return;

    //Berlekamp–Massey algorithm
    //register length
    int L = 0;

    //create locators polinom
    vect_int A(fs_, 0);
    int deg_A = 0;
    A[0] = 1;

    //create discrepancy compensating polynomial
    vect_int B(fs_, 0);
    B[0] = 1;

    int m = 0;
    for (int r = 1; r <= (d_ - 1); r++){
        int D = 0; //discrepancy
        for (int j = 0; j <= L; j++) D = S_ddtd_[D][M_ddtd_[A[j]][S[r - j - 1]]];
        
        if (D != 0){
            vect_int T(fs_, 0);
            T = mult_vect_to_one_element_vect_in_gf(B, (r - m), D, M_ddtd_, S_ddtd_, F_dtp_, F_ptd_, gen_pol_, n_);
            T = sum_vect_to_vect_in_gf(A, T, S_ddtd_);

            if ((2 * L) <= (r - 1)){
                int D_inv = F_ptd_[((n_ - F_dtp_[D]) % n_)];
                B = mult_vect_to_coef_in_gf(A, D_inv, M_ddtd_);
                L = r - L;
                m = r;
            }

            A = T;

        }
    }

    for(int i = (n_ - 1); i >= 0; i--){
        if (A[i] != 0){
            deg_A = i;
            break;
        }
    }

    //too many errors
    if (deg_A != L) return;

    // locate error positions
    vect_int errors;
    // if lambda(a^-x) = 0, there is an error in position x
    for (int i = 0; i < n_; i++) {
        int res = solve_poly_by_coef_in_gf(A, F_ptd_[i], M_ddtd_, S_ddtd_, F_ptd_, F_dtp_, n_);

        if (res == 0) {
            errors.push_back((n_ - i) % n_);
            if (errors.size() == L) break;
        }
    }

    // correct all errors
    for (int e : errors) word_in[e] = !word_in[e];
}

void decode(std::vector<bool>& word_in){ 

    //create Sindrome value vector polinom
    vect_int S((d_ - 1), 0);
    int count_not_zero_S = 0;

    for (int deg_prim = 0; deg_prim < d_ - 1; deg_prim++){
        int cur_S_val = 0;

        for (int deg_word_in = 0; deg_word_in < n_; deg_word_in++){
            if (word_in[deg_word_in]){
            cur_S_val = S_ddtd_[cur_S_val][F_ptd_[((deg_prim + b_) * deg_word_in) % n_]];
            }
        }
        
        if (cur_S_val != 0) count_not_zero_S++;
        S[deg_prim] = cur_S_val;
    }

    //doesn't have errors
    if (count_not_zero_S == 0) return;

    //Berlekamp–Massey algorithm
    //register length
    int L = 0;
    int m = 0;

    //create locators polinom
    vect_int A(1, 1);

    //create discrepancy compensating polynomial
    vect_int B(1, 1);
    
    for (int r = 1; r <= (d_ - 1); ++r){
        if (r % 2 == 0) continue;

        int D = 0; //discrepancy
        //int size_A = A.size();

        for (int j = 0; j <= L; j++) D = S_ddtd_[D][M_ddtd_[A[j]][S[r - j - 1]]];
        
        if (D == 0) continue;
        
        //int size_B = B.size();            
        vect_int T = A;
        T.resize(std::max(A.size(), (r - m + B.size())), 0);

        for (int i = 0; i < B.size(); ++i) T[r - m + i] = S_ddtd_[T[r - m + i]][M_ddtd_[D][B[i]]];

        while (T.size() > 1 && T.back() == 0) T.pop_back();
            

        if ((2 * L) <= (r - 1)){
            //B.clear();
            B = A;
            int D_inv = F_ptd_[((n_ - F_dtp_[D]) % n_)];

            for (int i = 0; i < B.size(); ++i) B[i] = (M_ddtd_[D_inv][B[i]]);

            L = r - L;
            m = r;
        }

        A = T;
        
    }

    //too many errors
    int size_A = A.size();
    if ((size_A - 1) != L) return;

    // locate error positions
    vect_int errors;
    // if lambda(a^-x) = 0, there is an error in position x
    for (int i = 0; i < n_; ++i) {
        int res = A[0];
        
        for (int l = 1; l < size_A; ++l){
            int mul = M_ddtd_[A[l]][F_ptd_[(i * l) % n_]];
            res = S_ddtd_[res][mul];
        } 

        if (res == 0) {
            errors.push_back((n_ - i) % n_);
            word_in[((n_ - i) % n_)] = !word_in[((n_ - i) % n_)];
            if (errors.size() == L) break;
        }
    }

    // // correct all errors
    // for (int e : errors) word_in[e] = !word_in[e];
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
                iters = i;

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