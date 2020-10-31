from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.toolbox.ABEnc import ABEnc
from msp import MSP


class AGGABE(ABEnc):

    def __init__(self, group_obj, verbose=False):
        ABEnc.__init__(self)
        self.group = group_obj
        self.util = MSP(self.group, verbose)

    def agg_setup(self, n):

        g = self.group.random(G1)
        beta_2 = self.group.random(ZR)
        alpha = self.group.random(ZR)
        a = self.group.random(ZR)
        b = self.group.random(ZR)
        c = self.group.random(ZR)
        v = g ** beta_2
        g_a = g ** a
        g_b = g ** b
        g_c = g ** c

        dic_g_i = {}
        for i in range(1, 2*n + 1):
            g_i = g ** (alpha ** i)
            dic_g_i[i] = g_i
            # print(i, dic_g_i[i])

        pk = {'g': g, 'v': v, 'n': n, 'g_i': dic_g_i, 'g_a': g_a, 'g_b': g_b, 'g_c': g_c}
        msk = {'a': a, 'b': b, 'c': c, 'beta_2': beta_2}
        return pk, msk

    def agg_keygen(self, pk, msk, attr_list, S):
        g = pk['g']
        # generate key for cs
        beta_1 = self.group.random(ZR)
        u = g ** beta_1
        # key_cs = {'pk_cs': u, 'sk_cs': beta_1}

        # generate key for dta owners
        dic_g_i = pk['g_i']
        # print(len(dic_g_i))
        n = pk['n']
        h_i_1 = {}  # n * n
        h_i_2 = {}  # n * 2n
        sk_i = {}
        for i in range(1, n+1):
            gama_i_1 = self.group.random(ZR)
            gama_i_2 = self.group.random(ZR)

            # print(i, dic_g_i[i])
            # h_i_1[i] = dic_g_i[i] ** gama_i_1
            # print('h_i_1', h_i_1)
            dic_h_1 = {}
            for j in range(1, n+1):
                temp_1 = dic_g_i[j] ** gama_i_1
                dic_h_1[j] = temp_1
            h_i_1[i] = dic_h_1

            ek_i_1 = u ** gama_i_1
            ek_i_2 = pk['v'] ** gama_i_1
            sk_i[i] = (ek_i_1, ek_i_2)
            # print('sk_i', sk_i)

            # h_i_2 = list_g_i[i] ** gama_i_2
            # iteration with 2n
            dic_h_2 = {}
            for j in range(1, 2*n + 1):
                # print(j)
                temp_2 = dic_g_i[j] ** gama_i_2
                # h_i_2[i][j] = h_j_2
                dic_h_2[j] = temp_2
            h_i_2[i] = dic_h_2
            # print('h_i_2', h_i_2)
            # pk_i[i] = (h_i_1, h_i_2)

        # generate key for users
        r = self.group.random(ZR)
        g_r = g ** r
        a = msk['a']
        b = msk['b']
        b_inverse = 1 / b
        c = msk['c']
        A_d = (a * c - r) * b_inverse
        A = g ** A_d

        A_B = {}
        for attr_j in attr_list:
            r_j = self.group.random(ZR)
            A_j = g_r * (self.group.hash(str(attr_j), G1) ** r_j)
            B_j = g ** r_j
            A_B[attr_j] = (A_j, B_j)

        # authorize user with DOs
        beta_2 = msk['beta_2']
        k_agg = 1
        for k in S:
            k_agg *= (dic_g_i[n + 1 - k] ** beta_2)
            # print('k_agg', k_agg)
        return {'attr_list': attr_list, 'pk_cs': u, 'sk_cs': beta_1, 'h_i_1': h_i_1, 'h_i_2': h_i_2, 'sk_i': sk_i, 'A': A, 'A_B': A_B, 'k_agg': k_agg}

    def agg_index(self, pk, key_gen, w_l, policy_list):
        n = pk['n']
        g = pk['g']
        v = pk['v']
        # pk_i = key['pk_i']
        # h_i_1 = key_gen['h_i_1']
        h_i_2 = key_gen['h_i_2']
        sk_i = key_gen['sk_i']

        # for each DO
        C_agg = {}
        W_all = {}
        W_agg = {}

        policy = {}
        for i in range(1, n + 1):
            r_i_l = self.group.random(ZR)
            # (h_i_1, h_i_2) = pk_i[i]
            # print(i, sk_i[i])
            (ek_i_1, ek_i_2) = sk_i[i]
            c_i_l_1 = ek_i_1 ** r_i_l
            c_i_l_2 = ek_i_2 ** r_i_l
            c_i_l_3 = (v * h_i_2[i][i]) ** r_i_l
            C_agg[i] = (c_i_l_1, c_i_l_2, c_i_l_3)

            # perform attribute based encryption
            policy[i] = self.util.createPolicy(policy_list[i])
            mono_span_prog = self.util.convert_policy_to_msp(policy[i])
            num_cols = self.util.len_longest_row

            u_bsw = []
            for j in range(num_cols):
                rand = self.group.random(ZR)
                u_bsw.append(rand)

            r_i_1 = self.group.random(ZR)
            r_i_2 = u_bsw[0]  # shared secret
            g_a = pk['g_a']
            g_b = pk['g_b']
            g_c = pk['g_c']
            W = g_c ** r_i_1
            W_0 = (g_a ** (r_i_1 + r_i_2)) * ((g_b ** (self.group.hash(str(w_l), ZR))) ** r_i_1)
            W_bar = g_b ** r_i_2
            W_all[i] = (W, W_0, W_bar)

            W_agg_i = {}
            for attr, row in mono_span_prog.items():
                cols = len(row)
                sum = 0
                for l in range(cols):
                    sum += row[l] * u_bsw[l]
                attr_stripped = self.util.strip_index(attr)
                W_f = g ** sum
                D_f = self.group.hash(str(attr_stripped), G1) ** sum
                W_agg_i[attr] = (W_f, D_f)
                W_agg[i] = W_agg_i
        return {'policy': policy, 'C_agg': C_agg, 'W_all': W_all, 'W_agg': W_agg}

    def agg_trap(self, pk, key_gen, w_l):
        x = self.group.random(ZR)
        s = self.group.random(ZR)

        Tr_1 = key_gen['k_agg'] * (pk['v'] ** x)
        Tr_2 = key_gen['pk_cs'] ** x
        tok_1 = (pk['g_a'] * (pk['g_b'] ** (self.group.hash(str(w_l), ZR)))) ** s
        tok_2 = pk['g_c'] ** s
        tok_3 = key_gen['A'] ** s

        A_B_bar = {}
        for attr_j in key_gen['attr_list']:
            (A_j, B_j) = key_gen['A_B'][attr_j]
            A_j_bar = A_j ** s
            B_j_bar = B_j ** s
            A_B_bar[attr_j] = (A_j_bar, B_j_bar)
        return {'Tr_1': Tr_1, 'Tr_2': Tr_2, 'tok_1': tok_1, 'tok_2': tok_2, 'tok_3': tok_3, 'A_B_bar': A_B_bar}

    def agg_search(self, pk, key_gen, S, I, Trap):
        h_i_2 = key_gen['h_i_2']  # dic
        # print(type(h_i_2))
        # print('n', pk['n'])
        flag1 = {}
        flag2 = {}
        for i in range(1, pk['n'] + 1):
            print('i', i)
            prod_pub = 1
            prod_k = 1
            dic_h_i_2 = h_i_2[i]  # dic
            # print(type(dic_h_i_2))
            for k in S:
                # (pub_1, pub_2) = key_gen['pk_i'][pk['n'] + 1 - k]
                # prod_pub *= pub_1
                h_i_1_k = key_gen['h_i_1'][i][pk['n'] + 1 - k]
                prod_pub *= h_i_1_k

                if k != i:
                    # (pk_1, pk_2) = key_gen['pk_i'][pk['n'] + 1 - k + i]
                    # prod_k *= pk_2
                    # h_i_2_k = h_i_2[[pk['n'] - 1 - k + i]][[pk['n'] - 1 - k + i]]
                    h_i_2_k = dic_h_i_2[pk['n'] + 1 - k + i]
                    prod_k *= h_i_2_k

            Tr_i_1 = Trap['Tr_1'] * prod_k

            # verify the eq.1
            (c_i_l_1, c_i_l_2, c_i_l_3) = I['C_agg'][i]
            # (h_1, h_2) = key_gen['pk_i'][pk['n'] + 1]
            h_2 = dic_h_i_2[pk['n'] + 1]
            left_1 = ((pair(prod_pub, c_i_l_3) ** key_gen['sk_cs']) * pair(c_i_l_2, Trap['Tr_2'])) / pair(Tr_i_1, c_i_l_1)
            right_1 = pair(h_2, c_i_l_1)

            if left_1 == right_1:
                flag1[i] = True
                print("The first layer satisfied.")

                nodes = self.util.prune(I['policy'][i], key_gen['attr_list'])
                if not nodes:
                    print("Policy not satisfied.")
                    # return None

                E_root = 1
                for node in nodes:
                    attr = node.getAttributeAndIndex()
                    attr_stripped = self.util.strip_index(attr)  # satisfied attributes
                    (A_j_bar, B_j_bar) = Trap['A_B_bar'][attr_stripped]
                    (W_f, D_f) = I['W_agg'][i][attr]
                    E_f = pair(A_j_bar, W_f) / pair(B_j_bar, D_f)
                    E_root *= E_f

                (W, W_0, W_bar) = I['W_all'][i]
                left_2 = pair(W_0, Trap['tok_2'])
                right_2 = pair(W, Trap['tok_1']) * E_root * pair(Trap['tok_3'], W_bar)

                if left_2 == right_2:
                    # return True
                    flag2[i] = True
                    print("The second layer satisfied.")
                else:
                    flag2[i] = False
                    print("The second layer not satisfied.")
                    # return False
            else:
                flag1[i] = False
                print("The first layer not satisfied.")
                # return False
        return {'flag1': flag1, 'flag2': flag2}


def main():
    print('## output test')
    pairing_group = PairingGroup('SS512')
    cpabe = AGGABE(pairing_group)
    # run set up
    print('---------Setup---------')
    (pk, msk) = cpabe.agg_setup(5)

    # run key generation
    print('---------KeyGen---------')
    attr_list = ['ONE', 'TWO', 'THREE']
    S = [1, 3]
    key_gen = cpabe.agg_keygen(pk, msk, attr_list, S)

    # set keyword set
    w_l = 'mingyue'

    # generate index
    print('---------Index---------')
    # 1: '((ONE and THREE) and (TWO OR FOUR))', 2: 'ONE OR FOUR', 3: 'ONE and THREE', 4: '((ONE and THREE) and (TWO OR FOUR))', 5: 'TWO OR FOUR'
    policy_str = {1: '((ONE and THREE) and (TWO OR FOUR))', 2: 'ONE OR FOUR', 3: 'ONE', 4: '((ONE and THREE) and (TWO OR FOUR))', 5: 'TWO OR FOUR'}
    I = cpabe.agg_index(pk, key_gen, w_l, policy_str)


    # generate trapdoor
    print('---------Trapdoor---------')
    Trap = cpabe.agg_trap(pk, key_gen, w_l)

    # match in 2 phases
    print('---------Search---------')
    re = cpabe.agg_search(pk, key_gen, S, I, Trap)
    print(re)

    # if flag == True:
    #     print("Successful search.")
    # else:
    #     print("Search failure.")


if __name__ == '__main__':
    main()