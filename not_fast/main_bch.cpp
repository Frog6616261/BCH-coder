#include <vector>
#include <fstream>
#include <iostream>
#include <string>
#include <set>
#include <random>

#define vect_b std::vector<bool>
#define vect_int std::vector<int>
#define vect_vect_int std::vector<std::vector<int>>
#define vect_vect_b std::vector<std::vector<bool>>

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
    
    vect_b encode(std::vector<int>& word_in){
        if (word_in.size() != k_) return vect_b();
    
        //create infom vector with degree n_ - k_ = r_
        vect_b result(n_, false);
    
        //fill n - k = r to n - 1
        for (int i = r_; i < n_ ; i++) result[i] = (word_in[i - r_] != 0);
    
        //find rest i(x) mod g(x)
        std::vector<bool> rest = result;
    
        for (int i = n_ - 1; i >= r_; --i){
            if (rest[i]){
                int num = 0;
                for (int j = r_; j >= 0; j--){
                    rest[i - num] = rest[i - num]^(g_[j] > 0);
                    num++;
                } 
            }
        }
    
        for (int i = r_ - 1; i >= 0; i--){
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
            
            if (cur_S_val != 0){
                count_not_zero_S++;
                S[deg_prim] = cur_S_val;
            } 
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
            if (r % 2 == 0) continue;
    
            size_t D = 0; //discrepancy
            //int size_A = A.size();
    
            for (size_t j = 0; j <= std::min(L, A.size()); j++) D ^= M_ddtd_[A[j]][S[r - j - 1]];
            
            if (D == 0) continue;
            
            //int size_B = B.size();            
            vect_int T = A;
            T.resize(std::max(A.size(), (r - m + B.size())), 0);
    
            for (size_t i = 0; i < B.size(); ++i) T[r - m + i] ^= M_ddtd_[D][B[i]];
    
            while (T.size() > 1 && T.back() == 0) T.pop_back();                
    
            if ((2 * L) <= (r - 1)){
                //B.clear();
                B.resize(A.size(), 0);
                size_t D_inv = F_ptd_[((n_ - F_dtp_[D]) % n_)];
    
                for (size_t i = 0; i < A.size(); ++i){
                    if (A[i] != 0) B[i] = (M_ddtd_[D_inv][A[i]]);
                    else B[i] = 0;
                } 

                A = T;
                L = r - L;
                m = r;
            }
            else A = T;
            
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
                res ^= mul;
            } 
    
            if (res == 0) {
                size_t cur_pos = (n_ - i) % n_;
                errors.push_back(cur_pos);
                word_in[cur_pos] = !word_in[cur_pos];
                if (errors.size() == L) break;
            }
        }    
    }
    
    template<typename T>
    inline void print_poly(std::vector<T>& poly, int size, std::ofstream& output_file){
        if (size > poly.size()){
            output_file << "ERROR" <<"\n";
            return;
        } 
    
        for (int i = 0; i < size; i++) output_file << poly[i]<< " ";

        output_file << "\n";
    }
    
    void print_code_gener_polinom(std::ofstream& output_file){
        print_poly(g_, (r_ + 1), output_file);
    }
    
    void print_k(std::ofstream& output_file){
        output_file << k_ <<"\n";
    }
    
    int get_k_(){
        return k_;
    }
    
    };
    
    
    
    int main(int argc, char* kwarg[]){
    
        //open files
        std::ifstream input_file ("input.txt");
        std::ofstream output_file ("output.txt");
    
        int n, a, d;
        input_file>>n;
        input_file>>a;
        input_file>>d;
    
        //create BCH object
        BCH code{n, a, d};
    
        //print paarametrs of code
        code.print_k(output_file);
        code.print_code_gener_polinom(output_file);
        int k = code.get_k_();
    
        //do the command
        std::string command;
        while(input_file.good()){

            input_file >> command;
            if (input_file.eof()) break;

            if (command == "Encode"){
                std::vector<int> word_in(k);
                std::vector<bool> word_out(n, false);
                for (size_t i = 0; i < k; i++) input_file >> word_in[i];

                word_out = code.encode(word_in);
                code.print_poly(word_out, n, output_file);
            }
    
            if (command == "Decode"){                
                std::vector<bool> word_in;
                int in_value{0};
                while (char(input_file.get()) != '\n' && input_file.good())
                {
                    input_file >> in_value;
                    word_in.push_back((in_value != 0));
                }
                code.decode(word_in);
                code.print_poly(word_in, n, output_file);
            } 
    
            if (command == "Simulate"){
                double snrb;
                int numb_of_simulations, max_error;
                input_file >> snrb >> numb_of_simulations >> max_error;
    
                std::vector<int> word_in(k);
                std::vector<bool> word_in_ch(n);
                std::vector<bool> word_out_ch(n);

                // random bits generator
                std::random_device rd;     // Only used once to initialise (seed) engine
                std::mt19937 rng{rd()};    // Random-number engine used (Mersenne-Twister in this case)
                
                std::uniform_int_distribution<> bits_distr{0, 1};
                std::bernoulli_distribution bsc{snrb};

                std::vector<int> code_word(k, 0);
                int total_codewords = 0;
                int total_codeword_errors = 0;
    
                for (size_t i_iter = 0; i_iter < numb_of_simulations; i_iter++){

                    for (size_t j = 0; j < k; j++) word_in[j] = bits_distr(rng);
                    word_in_ch = code.encode(word_in);
                    
                    //generete out vector               
                    for (int t = 0; t < n; t++){
                        if (bsc(rng)) word_out_ch[t] = !word_in_ch[t];
                        else word_out_ch[t] = word_in_ch[t];
                    }

                    code.decode(word_out_ch);
                    total_codewords += 1;
                    if (word_in_ch != word_out_ch) total_codeword_errors += 1;

                    if (total_codeword_errors > max_error) break;          
                }

                output_file << (double) total_codeword_errors / total_codewords << std::endl;
            } 
        }

        output_file.close();
        input_file.close();
    
        return 0;
    }