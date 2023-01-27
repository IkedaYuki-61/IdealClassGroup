from collections import deque, Counter, defaultdict
from math import gcd, atan2, degrees,floor, pi, sqrt #degrees(atan2(y,x)) 
from bisect import bisect_left,insort_left
from heapq import heapify, heappop, heappush
from copy import deepcopy
from itertools import permutations,product
import sys #再帰はpython
sys.setrecursionlimit(10**8)


class ideal_class_group:
    def __init__(self, m):
        if m > 0:
            print('実二次体は未実装')
            exit()
        elif m <= -3:
            i = 2
            while i*i <= m:
                if m % i**2 == 0:
                    print('Error : 平方因子を含んでいる')
                    exit()
                i += 1
            self.m = m
        else:
            print('m = 0,-1,-2 error')
            exit()

        if m%4==1:
            #omega = (sqrt(m)+1)/2
            self.l = (1-m)//4
            self.del_k = m
            #print('P(x) = x^2 + x +',self.l)
        else:
            #omega = sqrt(m)
            self.l = -m
            self.del_k = 4*m
            #print('P(x) = x^2 +',self.l) 

        if self.del_k > 0:
            self.Mk = sqrt(self.del_k)/2
        else:
            self.Mk = sqrt(-self.del_k)*2/pi

        self.make_reduce_list()     #self.reduce　の設定
        self.make_h()               #self.h　の設定
        self.make_Sk()              #self.Sk の設定
        self.make_Quad_res_list()   #self.Quad_res_list の設定 mySqrt用のリスト

        #print(prime_for_quad)
        
        #self.print_set_up()


    def check(self, x):
        for p in self.Sk:
            while x%p == 0:
                x //= p
        
        if x == 1:
            return True
        else:
            return False

    def p_chage_quad(self, p,x):
        if self.m%4 == 1:
            a = p
            b = 2*x + 1
            if self.f(x) % p != 0:
                print('f(x)/p error')
                print('f(x)/p = ',self.f(x)/p)
            c = self.f(x)//p
            if x > 0:
                print('[%d, ω+%d] = '%(p,x), end='')
            elif x == 0:
                print('[%d, ω  ] = '%(p), end='')
            else:
                print('[%d, ω-%d] = '%(p,-x), end='')

            print_f(make_reduced((a,b,c)))
        else:
            print('m%4 != 1 よりchange_quad未開発')
            exit()

    def f(self, x):
        if self.m%4==1:
            return x**2 + x + self.l
        else:
            return x**2 + self.l

    def make_h(self):
        if self.m < 0:
            self.h = len(self.reduce)
            """ l = -self.m #self.lとは異なる
            if l%2 == 0:
                print('jacob not odd error')
                exit()

            if l % 8 == 7:
                h = 0
                for z in range(1, (l + 1)//2):
                    #print(z,l,jacobi_symbol(z,l))
                    h += jacobi_symbol(z, l)
            else:
                h = 0
                for z in range(1, (l + 1)//2):
                    h += jacobi_symbol(z, l)
                h //= 3
            return  h """

        else:
            return 0

    def make_Sk(self):
        P = seachPrimeNum(int(self.Mk))
        self.Sk = []
        for p in P:
            #print(p, self.khi(p))
            if self.khi(p) == -1:
                continue
            self.Sk.append(p)
    
    def make_Quad_res_list(self):
        self.Quad_res_list = [] #my_rootに必要
        prime_for_quad = [256, 9]
        prime_for_quad.extend(seachPrimeNum(107))
        prime_for_quad.pop(2)
        for n in prime_for_quad:
            A = set()
            for i in range(n):
                A.add((i**2)%n)
            A = list(A)
            self.Quad_res_list.append([n,A])
    
    
    def khi(self, p):
        if p==2 and self.m%4==1:
            ans = (-1)**((self.del_k**2 -1)//8)
        elif self.del_k%p==0:
            ans = 0
        else:
            #ans = jacobi_symbol(self.del_k, p)
            ans = Leg(self.del_k, p)

        return ans

    def Kummer_1(self, p): #m%4==1 & X(p) != -1
        # return (b_1, b_2)   p_i = [p, b_i + ω]
        if p == 2:
            return (0,1)
        #p!=2
        h = (1+p)//2
        if self.m%p == 0:
            return (-h,-h)
        
        m_p = self.m%p
        for x in range(p):
            if (x**2)%p == m_p:
                a = x
                break
        x1 = -h-a*h
        x1 %= p
        x2 = -h+a*h
        x2 %= p
        if x1 > x2:
            x1,x2 = x2,x1
        return (x1, x2)

    def Kummer_23(self, p): #m%4==23 & X(p) != -1 mikaihatu
        if p == 2:
            if self.m % 4 == 2:
                return (0, 0)
            elif self.m % 4 == 3:
                return (1, 1)
            else:
                print('Kummer 2 3 error')
                exit()
        else:
            if self.m % p == 0:
                return (0, 0)
            else:
                if Leg(self.m, p) == 1:
                    a = -1
                    for i in range(p):
                        if i*i % p == self.m % p:
                            a = i
                            break
                    return (a, -a)
                else:
                    return (-1, -1) #(p)は既約

    def mysqrt(self, n):
        for i in range(len(self.Quad_res_list)):
            if n%self.Quad_res_list[i][0] not in self.Quad_res_list[i][1]:
                return None
        l = 0
        r = n
        while l <= r:
            m = (l + r) // 2
            m2 = m * m
            if m2 == n:
                return m
            if m2 > n:
                r = m - 1
            else:
                l = m + 1

    def output(self, b,Pb):
        A = prime_factorize(Pb)
        C = Counter(A)
        out = ''
        A = list(set(A))
        A.sort()
        for i in A:
            out += '('+str(i)+'^'
            out += str(C[i])
            out += ')'

        out += ' ~ '

        V = list(C.keys())
        V.sort()

        for v in V:
            out += '('
            if b%v <= (v-1)//2:
                out += '+1'
            else:
                out += '-1'
            out += ')'

        return out

    def print_bunkai(self, p,x1,x2):
        if x1 == 0:
            print('(%d) = [%d,ω][%d,ω+%d]'%(p,p,p,x2))
        elif x1 == x2:
            print('(%d) = [%d,ω+%d]^2'%(p,p,x1))
        else:
            print('(%d) = [%d,ω+%d][%d,ω+%d]'%(p,p,x1,p,x2))

    def print_set_up(self):
        print('h =',self.h)
        print('Mk =',self.Mk)
        print('Sk =',self.Sk)
        if self.m%4==1:
            quad_stack = []
            for p in self.Sk:
                x1,x2 = self.Kummer_1(p)
                self.print_bunkai(p, x1,x2)
                quad_stack.append((p,x1))
                quad_stack.append((p,x2-p))
            print()

            for p, x in quad_stack:
                self.p_chage_quad(p,x)
            print('P(x) = x^2 + x +',self.l)
        else:
            for p in self.Sk:
                x1,x2 = self.Kummer_23(p)
                self.print_bunkai(p, x1,x2)
            print('P(x) = x^2 +',self.l) 
        
        print()
        return

    def all_search(self):
        N = len(self.Sk)
        if N == 0:
            print('len(Sk)==0より構造不確定')
            exit()
        b_max = 0
        B = []
        #for E in product(range(2*h+1),repeat=N): #O((h^N))
        h = int((10**6)**(1/N))
        print('探索位数 h = %d'%h)
        for E in product(range(h),repeat=N):
            Pb = 1
            for i in range(N):
                Pb *= self.Sk[i]**E[i]
            if self.m+4*Pb < 0:
                continue

            b = self.mysqrt(self.m+4*Pb)
            if b == None:
                continue
            b -= 1

            if b%2 != 0:
                print('b even error')
                continue
            b //= 2
            b_max = max(b_max, b)
            if self.f(b) != Pb:
                print('f(b) != Pb')
                print(self.f(b),Pb)
                exit()

            B.append(b)
        
        B.sort()
        for b in B:
            Pb = self.f(b)
            print('P(%d) = %d = %s' %(b,Pb ,self.output(b,Pb)))

        print('Total :',len(B))
        print('Max b :',b_max)
        print('%d : %d : %d : %d :'%(self.m, len(self.Sk), len(B), b_max),self.Sk)

    def pell_eq(self):
        D = make_divisors(self.h)
        #print(D)
        stack = []
        if self.m % 4 == 1:
            # p^d = N(x+yω) = x^2 + xy + l*y^2
            # 4*p^d = (2x+y)^2 - m*y^2
            # R = u^2 + L*v^2
            for p in self.Sk:
                flag_d = False
                for d in D:
                    if d == 1:
                        continue
                    R = 4*(p**d)
                    v = 0
                    while R + self.m*(v**2) >= 0:
                        #print(R,self.m,(v**2))
                        u = self.mysqrt(R + self.m*(v**2))
                        if u == None:
                            v += 1
                            continue
                        print('u,v =',u,v)
                        print('x,y =',(u-v)/2,v)
                        stack.append(d)
                        flag_d = True
                        break

                    """  n = int((sqrt(4*(p**d)/(-self.m))))+1
                    #print(n)
                    
                    for v in range(1,n):
                        u2 = 4*(p**d) + self.m*(v**2)
                        u = sqrt(u2)
                        #print(u)
                        if int(u) == u:
                            #print('p = %d,  d = %d'%(p,d))
                            #print('%d**2 + %d*(%d**2) = 4*(%d**%d)'%(u,-self.m,v,p,d))
                            stack.append(d)
                            flag_d = True
                            break 
                    """
                    if flag_d:
                        break
                if not flag_d:
                    stack.append(-1)
        else:
            # p^d = N(x+yω) = x^2 + l*y^2
            # R = u^2 + L*v^2
            for p in self.Sk:
                flag_d = False
                for d in D:
                    if d == 1:
                        continue
                    y = 0
                    while p**d - self.l*(y**2) >= 0:
                        x = self.mysqrt(p**d - self.l*(y**2))
                        if x == None:
                            y += 1
                            continue
                        print('x, y =',x,y)
                        stack.append(d)
                        flag_d = True
                        break

                    if flag_d:
                        break
                if not flag_d:
                    stack.append(-1)
        print(self.Sk)
        print(stack)
        if max(stack) != self.h:
            return True
        return False
    
    def all_Sk_order(self):
        order_list = []
        for p in self.Sk:
            D = make_divisors(self.h)
            for d in D:
            #for time in range(1,h+1):
                P = self.prod_any_prime_ideal((p,d), (p,0))
                #print(self.p_change_reduce(P))
                if self.p_change_reduce(P)[0] == 1:
                    order_list.append(d)
                    break
        
        return order_list

        #print(self.Sk)
        #print(order_list)
        """ print('Sk'.ljust(6, ' '),end=' : ')
        for i in range(len(self.Sk)):
            if i == len(self.Sk)-1:
                print(str(self.Sk[i]).ljust(3, " "))
            else:
                print(str(self.Sk[i]).ljust(3, " "), end=', ')
        print('order'.ljust(6, ' '),end=' : ')
        for i in range(len(order_list)):
            if i == len(order_list)-1:
                print(str(order_list[i]).ljust(3, " "))
            else:
                print(str(order_list[i]).ljust(3, " "), end=', ')
        if len(order_list) != len(self.Sk):
            print('error : order_list生成失敗')
            exit()
        if min(order_list) == 1:
            print('error : order = 1 khi(p) = -1?') """
        if max(order_list) < self.h:
            return max(order_list)
        else:
            return -1
    
    def print_Sk_and_order(self):
        order_list = self.all_Sk_order()
        print('Sk'.ljust(6, ' '),end=' : ')
        for i in range(len(self.Sk)):
            if i == len(self.Sk)-1:
                print(str(self.Sk[i]).ljust(3, " "))
            else:
                print(str(self.Sk[i]).ljust(3, " "), end=', ')
        print('order'.ljust(6, ' '),end=' : ')
        for i in range(len(order_list)):
            if i == len(order_list)-1:
                print(str(order_list[i]).ljust(3, " "))
            else:
                print(str(order_list[i]).ljust(3, " "), end=', ')
        if len(order_list) != len(self.Sk):
            print('error : order_list生成失敗')
            exit()
        if min(order_list) == 1:
            print('error : order = 1 khi(p) = -1?')

    def Analysis_structure(self, mode):
        #D = make_divisors(self.h)
        P = prime_factorize(self.h)
        c = Counter(P)
        Prime_factor = list(c.keys())
        Prime_factor.sort()
        order_list = self.all_Sk_order()
        max_d_order_list = []
        for d in Prime_factor:
            max_d_order = d
            ord_cnt = 1
            for ord in order_list:
                flag = False
                while ord % (d * max_d_order) == 0:
                    max_d_order *= d
                    ord_cnt += 1
                    if ord_cnt == c[d]:
                        flag = True
                        break
                if flag:
                    break
            max_d_order_list.append(ord_cnt)

        if mode == 1:
            group_key = 1
            for i in range(len(max_d_order_list)):
                group_key *= Prime_factor[i] ** max_d_order_list[i]
            return group_key
        elif mode == 2:
            flag = False
            for i in range(len(Prime_factor)):
                if max_d_order_list[i] != c[Prime_factor[i]]:
                    flag = True
                    break
            
            if flag:
                print('m = %d ≡ %d (mod 4)'%(self.m, self.m%4))
                print('Prime_facotr'.ljust(12, ' '),end=' : ')
                print(*Prime_factor)
                print('max_d_order'.ljust(12, ' '),end=' : ')
                print(*max_d_order_list)
                print()
                return -1 #巡回群でない
            else:
                return 1 #巡回群
        elif mode == 3:#巡回群かの判定（出力なし）
            for i in range(len(Prime_factor)):
                if max_d_order_list[i] != c[Prime_factor[i]]:
                    return False #巡回群でない
            return True #巡回群
            

        else:
            return
         
        """ print('Prime_facotr'.ljust(12, ' '),end=' : ')
        print(*Prime_factor)
        print('max_d_order'.ljust(12, ' '),end=' : ')
        print(*max_d_order_list) """


        


    def p_change_reduce(self,P):
        # [p, b+ω] = (a, b, c):二次形式 ~ (a, b, c):簡約二次形式
        p,b = P
        #print('p_change',p,b,self.f(b))
        if self.m % 4 == 1:
            if self.f(b)%p != 0:
                print('p_change_reduce error (f(b)%p!=0)')
                print(p,2*b+1,self.f(b)//p,'...',self.f(b)%p)
                exit()
            #print(p,2*b+1,self.f(b)//p)
            return make_reduced((p, 2*b+1, self.f(b)//p))
            
        else:
            #print(P)
            if self.f(b)%p != 0:
                print('p_change_reduce error (f(b)%p != 0)')
                print(p,2*b,self.f(b)//p,'...',self.f(b)%p)
                exit()

            #print(p,2*b+1,self.f(b)//p)
            return make_reduced((p, 2*b, self.f(b)//p))
    
    def change_complex(self):
        C = []
        for a,b,c in self.reduce:
            #C.append((-b/(2*a), ((abs(self.del_k))**(1/2))/(2*a) ))
            C.append((b/(2*c), ((abs(self.del_k))**(1/2))/(2*c) ))
        return C


    def all_Sk_prod(self):
        N = len(self.Sk)
        if N < 2:
            print('len(Sk) =',N)
            exit()
        if self.m%4 == 1:
            for i in range(N):
                p = self.Sk[i]
                xp,yp = self.Kummer_1(p)
                P = (p,xp)
                #F = self.p_change_reduce(p, xp)

                for j in range(i,N):
                    q = self.Sk[j]
                    xq,yq = self.Kummer_1(q)
                    Q = (q,xq)
                    #G = self.p_change_reduce(q,xq)
                    #FG = prod_quad_form(F, G)
                    '''for i in range(p*q):
                        if xp%p == i and xq%q == i:
                            x = i
                            break'''
                    print('[%d,ω+%d][%d,ω+%d] = '%(p,xp,q,xq),end='')
                    pq,c = self.prod_prime_ideal(P,Q)
                    print('[%d,%d+ω] = '%(pq,c),end='')
                    print('(%d, %d, %d) = '%(pq,2*c+1,self.f(c)/pq),end='')
                    print(self.p_change_reduce((pq,c)))
                    '''if self.f(x) % x != 0:
                        print('f(x) mod x != 0')
                        print(self.f(x))
                        exit()
                    FG = make_reduced((p*q, 2*x+1, self.f(x)//x))
                    
                    print(F,G,'= ',end='')
                    print((p*q, 2*x+1, self.f(x)//x),'= ',end='')
                    print(FG)'''
        else:
            print('all Sk prod m%4==2,3 未実装')
            pass

    def prod_prime_ideal(self, P,Q):
        p, a = P #[p,o+a]
        q, b = Q #[q,o+b]
        a %= p
        b %= q
        pq = p*q
        a %= pq
        b %= pq
        if p < q:
            p,q = q,p
            a,b = b,a
        # 以下 p > q 
        #print('変換前',p,a,' ',q,b)
        if p == q:
            if self.m % 4 == 1:
                #  [p^2, p(o+a), o^2+(a+a)o+aa  ]
                # =[p^2, po+ap , (2a+1)o+(a^2-l)]
                q = 2*a+1
                b = a*a - self.l
                b %= pq                
                a = a*p
                #print('p=q変換',p,a,' ',q,b)
            else:
                #  [p^2, p(o+a), o^2+(a+a)o+aa]
                # =[p^2, po+ap , (2a)o+(a^2-l)]
                q = 2*a
                b = a*a - self.l
                b %= pq                
                a = a*p
             
        elif p % q == 0:
            #   [pq, p(o+b), q(o+a), o^2+(a+b)o+ab]
            x = (p*(b-a))%pq
            if x != 0:
                #p(o+b) - p(o+a) = p(b-a)
                if pq % x == 0:
                    pq = x
                else:
                    if gcd(pq,x) != 1:
                        print('Not tagainiso error 468')
                        exit()
                    return (1,1) ###要確認

            if self.m % 4 == 1:
                # = [pq, qo+aq, (a+b+1)o+(ab-l)]
                # ~ [pq, qo+b,      p  o+  a   ]
                p,a,b = a+b+1, a*b-self.l, a*q
                #print('p%q変換',p,a,' ',q,b)
            else:
                # = [pq, qo+aq, (a+b)o+(ab-l)]
                # ~ [pq, qo+b,    p  o+  a   ]
                p,a,b = a+b, a*b-self.l, a*q
        else:
            # [pq, p(o+b), q(o+a), ...]
            a *= q
            b *= p
            p,q = q,p
        
        a %= pq
        b %= pq

        if p < q:
            p,q = q,p
            a,b = b,a
        
        #print('変換中',pq,' ', p,a,' ',q,b)
        # p > q
        if p*q == 0: ####要証明####
            return (1, 1)
        if p % q == 0:
            # [pq, po+a, qo+b, ...]
            k = p//q
            x = (a-k*b)%pq
            if x != 0:
                pq = gcd(pq, x)
            b %= pq
            # [pq, qo+b]
            if q == 1:
                return (pq, b)
            else:
                if not (pq%q == 0 and b%q == 0):
                    print('okasii 481gyoume')
                    exit()
                return (pq//q, b%q)

        #以下 p > q [p*q, qo+qa, po+pb, ...]
        #print('変換後', p,a,' ',q,b)
        while q != 1:
            s, p = divmod(p,q)
            a -= s*b
            a %= pq
            p,q = q,p
            a,b = b,a
            #print(p,a,q,b)
        return (pq, b%pq)
    
    def from_prod_ideal_to_quad(self,P,Q):
        return self.p_change_reduce(self.prod_prime_ideal(P,Q))

    def prod_any_prime_ideal(self,P,Q):
        # 戻り値 : [p, b + ω] -> (p, b)
        p, pow_p = P    # Pは単位でない素イデアル
        q, pow_q = Q
        if not (p in self.Sk and q in self.Sk):
            if p == 1 and q == 1:
                return (1, 0)   # [1, ω] = (1)
            elif p == 1:
                pow_p = 0
            elif q == 1:
                pow_q = 0
            else:
                print('Sk error(prod_any_prime_ideal)')
                exit()
        if pow_p == 0:
            print('error  pow_p == 0 ')
            exit()
        
        if self.m % 4 == 1:
            a = self.Kummer_1(p)[0]
            b = self.Kummer_1(q)[0]
            P = (p,a)
            Q = (q,b)
            for _ in range(pow_p-1):
                P = self.prod_prime_ideal(P,(p,a))
            if pow_q == 0:
                return P
            for _ in range(pow_q-1):
                Q = self.prod_prime_ideal(Q,(q,b))
            return self.prod_prime_ideal(P,Q)
        else:
            a = self.Kummer_23(p)[0]
            b = self.Kummer_23(q)[0]
            if a == -1 and b == -1:
                return (1, 0)
            elif a == -1:
                p,q = q,p
                pow_p, pow_q = pow_q, pow_q
                a,b = b,a
                pow_q = 0
            elif b == -1:
                pow_q = 0

            P = (p, a) # = [p, ω+a]
            Q = (q, b) # = [q, ω+b]
            #print(P,pow_p,' ', Q, pow_q)
            for _ in range(pow_p-1):
                P = self.prod_prime_ideal(P,(p,a))
            if pow_q == 0:
                return P
            for _ in range(pow_q-1):
                Q = self.prod_prime_ideal(Q,(q,b))
            return self.prod_prime_ideal(P,Q)

    def make_reduce_list(self):
        self.reduce = []
        D = self.m
        if self.m % 4 != 1:
            D *= 4

        if D < 0:
            k = int(sqrt(-D/3))
            cnt = 0
            for b in range(k+1)[D%2::2]:
                ac = (b*b-D)//4
                div_list = make_divisors(ac)
                for a in div_list:
                    c = ac//a
                    if a > c:
                        break

                    if a == c:
                        if b <= a:
                            self.reduce.append((a,b,c))
                            #print((a,b,c))
                            #print_f((a,b,c))
                            cnt += 1
                    else: # a < c
                        if a == b:
                            self.reduce.append((a,b,c))
                            #print((a,b,c))
                            #print_f((a,b,c))
                            cnt += 1
                        elif b == 0:
                            self.reduce.append((a,b,c))
                            #print((a,b,c))
                            #print_f((a,b,c))
                            cnt += 1                    
                        elif b < a:
                            self.reduce.append((a,b,c))
                            self.reduce.append((a,-b,c))
                            #print((a,b,c))
                            #print((a,-b,c))
                            #print_f((a,b,c))
                            #print_f((a,-b,c))
                            cnt += 2
            self.reduce.sort(lambda x: (x[0], -x[1]))

        else:
            print('D >= 0 は未実装')
            pass

    def list_up_reduce(self):
        for i in range(len(self.reduce)):
            print(self.reduce[i])
        print('total : %d'%len(self.reduce))

    def list_up_all_Sk_pow_reduced(self):
        self.reduce_dict = defaultdict(tuple)
        self.reduce_dict[(1,1,self.l)] = (1,0,1)
        if self.m %4 == 1:
            for p in self.Sk:
                x1,x2 = self.Kummer_1(p)
                i = 1
                P = (p,x1)
                while True:
                    if i != 1:
                        P = self.prod_prime_ideal(P,(p,x1))
                    #print(P)
                    if self.p_change_reduce(P)[0] == 1:
                        break
                    print('[%d,ω+%d]^%d = '%(p,x1,i),end='')
                    #print('[%d,ω+%d] = '%P,end='')
                    F = self.p_change_reduce(P)
                    print(F)
                    if not self.reduce_dict[F]:
                        self.reduce_dict[F] = (p,x1,i)
                    i += 1
            
            #print(self.reduce_dict)

        else:   
            for p in self.Sk:
                x1,x2 = self.Kummer_23(p)
                i = 1
                P = (p,x1)
                while True:
                    #print('hoge')
                    if i != 1:
                        P = self.prod_prime_ideal(P,(p,x1))
                    #print(P)
                    if self.p_change_reduce(P)[0] == 1:
                        if i == 2:
                            print('[%d,ω+%d]^%d = (1, 0, %d)'%(p,x1,i,self.l))
                        break
                    print('[%d,ω+%d]^%d = '%(p,x1,i),end='')
                    #print('[%d,ω+%d] = '%P,end='')
                    F = self.p_change_reduce(P)
                    print(F)
                    if not self.reduce_dict[F]:
                        self.reduce_dict[F] = (p,x1,i)
                    i += 1
            
            print(self.reduce_dict)
            


    


###素数列挙
def seachPrimeNum(N):
    if N == 1:
        return []
    max = int(sqrt(N))
    seachList = [i for i in range(2,N+1)]
    primeNum = []
    while seachList[0] <= max:
        primeNum.append(seachList[0])
        tmp = seachList[0]
        seachList = [i for i in seachList if i % tmp != 0]
    primeNum.extend(seachList)
    return primeNum

###素因数分解
def prime_factorize(n):
    a = [] #12-> a= [2,2,3]->個数はCounter
    while n % 2 == 0:
        a.append(2)
        n //= 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            a.append(f)
            n //= f
        else:
            f += 2
    if n != 1:
        a.append(n)
    return a

def jacobi_symbol(a, n):
    if n < 0 or not n % 2:
        print("n should be an odd positive integer")
        #raise ValueError("n should be an odd positive integer")
        return 0
    if a < 0 or a > n:
        a = a % n
    if n == 1 or a == 1:
        return 1
    if gcd(a, n) != 1:
        return 0

    j = 1
    if a < 0:
        a = -a
        if n % 4 == 3:
            j = -j
    while a != 0:
        while a % 2 == 0 and a > 0:
            a >>= 1
            if n % 8 in (3, 5):
                j = -j
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            j = -j
        a %= n
    if n != 1:
        j = 0
    return j

def Leg(a, p):
    a %= p
    #print('a, p, a%p =',a, p, a%p)
    if a==0:
        return 0
    for x in range(p):
        if (x**2)%p == a:
            #print(x**2,(x**2)%p,a)
            return 1
    return -1

###約数列挙
def make_divisors(n):
    divisors = []
    for i in range(1, int(n**0.5)+1):
        if n % i == 0:
            divisors.append(i)
            if i != n // i:
                divisors.append(n//i)
    divisors.sort()
    return divisors


def print_f(F):
    a,b,c = F
    '''if not(-a < b <= a < c or 0 <= b <= a == c):
        print('reduce error')'''
        #exit()

    print('(%d, %d, %d)'%(a,b,c))
    return
    
    """ if a == 1:
        A = ''
    else:
        A = str(a)
    if abs(b) == 1:
        B = ''
    else:
        B = str(abs(b))
    if c == 1:
        C = ''
    else:
        C = str(c)

    if b == 0:
        print('%sx^2 + %sy^2' %(A,C))
    elif b > 0:
        print('%sx^2 + %sxy + %sy^2' %(A,B,C))
    else:
        print('%sx^2 - %sxy + %sy^2' %(A,B,C)) """

def print_time(start_time,end_time):
    elapsed_time = end_time - start_time
    if elapsed_time<60:
        print('%fs'%elapsed_time)
    elif 60<= elapsed_time < 3600:
        m,s = divmod(elapsed_time, 60)
        print('%dm %ds'%(m,s))
    else:
        m,s = divmod(elapsed_time, 60)
        h,m = divmod(m, 60)
        print('%dh %dm %ds'%(h,m,s))


def prod_quad_form(F,G):
    a,b,c = make_reduced(F)
    d,e,f = make_reduced(G)

    D = b*b - 4*a*c
    if e*e - 4*d*f != D:
        print('D error')
        exit()
    
    B = -1
    cnt = 0
    for i in range(2*a*d):
        if i % (2*a) != b%(2*a):
            continue
        if i % (2*d) != e%(2*d):
            continue 
        if (i*i) % (4*a*d) != D%(4*a*d):
            continue
        B = i
        #print(i)
        cnt += 1
    
    if cnt >= 2:
        print('B is not unit :',cnt)
        exit()
    if B == -1:
        print('B is not found')
        exit()

    A = a*d
    C = (B**2 - D)//(4*A)

    return make_reduced((A,B,C))

def make_reduced(F):
    #print(F,'make_reduce')
    a,b,c = F
    if a <= 0:
        print('a is negative')
        exit()
    
    D = b*b - 4*a*c

    if D >= 0:
        print('D is positive')
        exit()

    #FF = (-1,-1,-1)
    while True:
        if  a > c:
            a,b,c = c,-b,a
        elif a == c:
            if b < 0:
                a,b,c = c,-b,a


        """ print(a,b,c)
        if FF == (a,b,c):
            exit()
        else:
            FF = (a,b,c) """

        if -a < b <= a < c or 0 <= b <= a == c:
            return (a, b, c)

        if b > c:        
            z = (-b+c)//(2*c)
            a, b, c = a+ b*z+ c*z**2, b+2*c*z, c
        else:
            z = (-b+a)//(2*a)
            a, b, c = a, b+2*a*z, c+b*z+a*z**2
        
    """ aa,bb,cc = a,b,c
    change = []
    if aa < cc:
        change.append(0)
        aa,cc = cc,aa
    while not(2*aa >= 2*cc >= bb and aa >= bb):
        #print('aa,bb,cc = %d, %d, %d'%(aa,bb,cc))
        change.append(1)
        aa,bb = aa-bb+cc, bb-2*cc
        if aa < cc:
            change.append(0)
            aa,cc = cc,aa
    #print('aa,bb,cc = %d, %d, %d'%(aa,bb,cc))
    #print(change)
    x0 = 0
    y0 = 1
    for i in range(len(change))[::-1]:
        if change[i] == 0:
            x0,y0 = y0,x0
        else:
            y0 += -x0
    n = cc
    #print(x0,y0,n)

    #print(x0,y0,n)
    p,q = xgcd(x0, y0)
    #print(p,q)
    B = -2*a*x0*q + b*(x0*p-y0*q) + 2*c*y0*p
    #print(-2*a*x0*q , b*(x0*p-y0*q) , 2*c*y0*p)
    C = a*(q**2) - b*p*q + c*(p**2)
    z = B/(2*n) + 0.5
    z = floor(z)
    if abs(B - 2*n*z) > n:
        print('z error')
        exit()
    BB = B-2*n*z
    if n == 1 and BB == -1:
        BB += 2
    CC = n*(z**2) - B*z + C
    if not (-n < BB <= n < CC or 0 <= BB <= n == CC):
        print('Faild make reduce')
        #exit()
    return (n ,BB, CC) """
    
def quad_f(F, x, y):
    a,b,c = F
    return a*(x**2) + b*x*y + c*(y**2)

def xgcd(a,b): # ax + by = 1
    x = a
    y = b
    if a*b == -1:
        return (a+1)//2,(b+1)//2
    if a*b == 1:
        return a,0 
    prevx, nextx = 1, 0
    prevy, nexty = 0, 1
    while b:
        quotient = a//b
        nextx, prevx = prevx - quotient * nextx, nextx
        nexty, prevy = prevy - quotient * nexty, nexty
        a, b = b, a % b
        #print(a,b)
    if prevx*x + prevy*y != 1:
        if prevx*x + prevy*y == -1:
            prevx *= -1
            prevy *= -1
        else:
            print('ax+by!=1 error')
            exit() 
    return prevx, prevy







    
def main():
    print('m = ',end='')
    m = int(input())
    Hk = ideal_class_group(m)
    """ print(Hk.mysqrt(100))
    print(Hk.mysqrt(10))
    exit() """
    Hk.list_up_reduce()
    print(Hk.Sk)
    print(len(Hk.Sk))
    #Hk.all_search()
    #Hk.all_Sk_prod()
    Hk.print_set_up()
    #Hk.pell_eq()
    #Hk.all_Sk_order()
    Hk.print_Sk_and_order()
    Hk.Analysis_structure(2)
    Hk.list_up_all_Sk_pow_reduced()
    '''while True:
        print('prod_1 = (p,pow_p) = ',end='')
        p,pow_p = map(int, input().split())
        if p == -1:
            exit()
        print('prod_2 = (q,pow_q) = ',end='')
        q,pow_q = map(int, input().split())
        xp = Hk.Kummer_1(p)[0]
        xq = Hk.Kummer_1(q)[0]
        print('[%d,ω+%d]^%d * [%d,ω+%d]^%d = '%(p,xp,pow_p, q,xq,pow_q),end='')
        pq,c = Hk.prod_any_prime_ideal((p,pow_p),(q,pow_q))
        print('[%d,%d+ω] = '%(pq,c),end='')
        print('(%d, %d, %d) = '%(pq,2*c+1,Hk.f(c)/pq),end='')
        print(Hk.p_change_reduce((pq,c)))'''
        

    '''print('m-list = ',end='')
    m_list = map(int, input().split(','))
    non_cycle = []
    for m in m_list:
        print('m =',-m)
        if -m % 4 != 1:
            print('-m mod 4 != 1')
            print()
            continue
        if m%8 == 0:
            print('m mod 8 == 0')
            print()
            continue
        Hk = ideal_class_group(-m)
        #Hk.all_search()
        #Hk.all_Sk_prod()
        #Hk.print_set_up()
        if Hk.pell_eq():
            non_cycle.append(m)
        print()
    
    print(non_cycle)
    print('num =',len(non_cycle))'''

    '''print('f = (a,b,c) = ',end='')
    F = tuple(map(int, input().split()))
    #a,b,c = map(int, input().split())
    print('g = (a,b,c) = ',end='')
    G = tuple(map(int, input().split()))
    #d,e,f = map(int, input().split())
    print_f(prod_quad_form(F,G))'''

    #print(make_reduced((49,17,65)))

    return



if __name__ == '__main__':
    main()
