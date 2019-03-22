#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sys
get_ipython().system('{sys.executable} -m pip install ipython')


# In[2]:


def phred33ToQ (qual):
    return ord(qual)-33


# In[3]:


def readFastq(filename):
    sequences = []
    qualities = []
    with open(filename) as fh:
        while True:
            fh.readline()  # skip name line
            seq = fh.readline().rstrip()  # read base sequence
            fh.readline()  # skip placeholder line
            qual = fh.readline().rstrip()  # base quality line
            if len(seq) == 0:
                break
            sequences.append(seq)
            qualities.append(qual)
    return sequences, qualities


# In[4]:


import string


def z_array(s):
    """ Use Z algorithm (Gusfield theorem 1.4.1) to preprocess s """
    assert len(s) > 1
    z = [len(s)] + [0] * (len(s)-1)

    # Initial comparison of s[1:] with prefix
    for i in range(1, len(s)):
        if s[i] == s[i-1]:
            z[1] += 1
        else:
            break
    
    r, l = 0, 0
    if z[1] > 0:
        r, l = z[1], 1

    for k in range(2, len(s)):
        assert z[k] == 0
        if k > r:
            # Case 1
            for i in range(k, len(s)):
                if s[i] == s[i-k]:
                    z[k] += 1
                else:
                    break
            r, l = k + z[k] - 1, k
        else:
            # Case 2
            # Calculate length of beta
            nbeta = r - k + 1
            zkp = z[k - l]
            if nbeta > zkp:
                # Case 2a: zkp wins
                z[k] = zkp
            else:
                # Case 2b: Compare characters just past r
                nmatch = 0
                for i in range(r+1, len(s)):
                    if s[i] == s[i - k]:
                        nmatch += 1
                    else:
                        break
                l, r = k, r + nmatch
                z[k] = r - k + 1
    return z


def n_array(s):
    """ Compile the N array (Gusfield theorem 2.2.2) from the Z array """
    return z_array(s[::-1])[::-1]


def big_l_prime_array(p, n):
    """ Compile L' array (Gusfield theorem 2.2.2) using p and N array.
        L'[i] = largest index j less than n such that N[j] = |P[i:]| """
    lp = [0] * len(p)
    for j in range(len(p)-1):
        i = len(p) - n[j]
        if i < len(p):
            lp[i] = j + 1
    return lp


def big_l_array(p, lp):
    """ Compile L array (Gusfield theorem 2.2.2) using p and L' array.
        L[i] = largest index j less than n such that N[j] >= |P[i:]| """
    l = [0] * len(p)
    l[1] = lp[1]
    for i in range(2, len(p)):
        l[i] = max(l[i-1], lp[i])
    return l


def small_l_prime_array(n):
    """ Compile lp' array (Gusfield theorem 2.2.4) using N array. """
    small_lp = [0] * len(n)
    for i in range(len(n)):
        if n[i] == i+1:  # prefix matching a suffix
            small_lp[len(n)-i-1] = i+1
    for i in range(len(n)-2, -1, -1):  # "smear" them out to the left
        if small_lp[i] == 0:
            small_lp[i] = small_lp[i+1]
    return small_lp


def good_suffix_table(p):
    """ Return tables needed to apply good suffix rule. """
    n = n_array(p)
    lp = big_l_prime_array(p, n)
    return lp, big_l_array(p, lp), small_l_prime_array(n)


def good_suffix_mismatch(i, big_l_prime, small_l_prime):
    """ Given a mismatch at offset i, and given L/L' and l' arrays,
        return amount to shift as determined by good suffix rule. """
    length = len(big_l_prime)
    assert i < length
    if i == length - 1:
        return 0
    i += 1  # i points to leftmost matching position of P
    if big_l_prime[i] > 0:
        return length - big_l_prime[i]
    return length - small_l_prime[i]


def good_suffix_match(small_l_prime):
    """ Given a full match of P to T, return amount to shift as
        determined by good suffix rule. """
    return len(small_l_prime) - small_l_prime[1]


def dense_bad_char_tab(p, amap):
    """ Given pattern string and list with ordered alphabet characters, create
        and return a dense bad character table.  Table is indexed by offset
        then by character. """
    tab = []
    nxt = [0] * len(amap)
    for i in range(0, len(p)):
        c = p[i]
        assert c in amap
        tab.append(nxt[:])
        nxt[amap[c]] = i+1
    return tab


# In[5]:


class BoyerMoore(object):
    """ Encapsulates pattern and associated Boyer-Moore preprocessing. """

    def __init__(self, p, alphabet='ACGT'):
        # Create map from alphabet characters to integers
        self.amap = {alphabet[i]: i for i in range(len(alphabet))}
        # Make bad character rule table
        self.bad_char = dense_bad_char_tab(p, self.amap)
        # Create good suffix rule table
        _, self.big_l, self.small_l_prime = good_suffix_table(p)

    def bad_character_rule(self, i, c):
        """ Return # skips given by bad character rule at offset i """
        assert c in self.amap
        assert i < len(self.bad_char)
        ci = self.amap[c]
        return i - (self.bad_char[i][ci]-1)

    def good_suffix_rule(self, i):
        """ Given a mismatch at offset i, return amount to shift
            as determined by (weak) good suffix rule. """
        length = len(self.big_l)
        assert i < length
        if i == length - 1:
            return 0
        i += 1  # i points to leftmost matching position of P
        if self.big_l[i] > 0:
            return length - self.big_l[i]
        return length - self.small_l_prime[i]

    def match_skip(self):
        """ Return amount to shift in case where P matches T """
        return len(self.small_l_prime) - self.small_l_prime[1]


# In[6]:


def boyer_moore(p, p_bm, t):
    """ Do Boyer-Moore matching """
    i = 0
    occurrences = []
    while i < len(t) - len(p) + 1:
        shift = 1
        mismatched = False
        for j in range(len(p)-1, -1, -1):
            if p[j] != t[i+j]:
                skip_bc = p_bm.bad_character_rule(j, t[i+j])
                skip_gs = p_bm.good_suffix_rule(j)
                shift = max(shift, skip_bc, skip_gs)
                mismatched = True
                break
        if not mismatched:
            occurrences.append(i)
            skip_gs = p_bm.match_skip()
            shift = max(shift, skip_gs)
        i += shift
    return occurrences


# In[8]:


from Bio import SeqIO
handle = open("Desktop/TGB_work/SBT_THA_mutation/client1_ThaMuv7_T0023.ab1", "rb")
record=SeqIO.read(handle, "abi")
t = record.annotations['abif_raw']['PBAS2'] 
k = record.annotations['abif_raw']['PCON2']  
p_32 = 'CATAAAA'
p_bm_32 = BoyerMoore(p_32, alphabet='ACGT')
p_32_position=boyer_moore(p_32, p_bm_32, t)
if p_32_position+[1]==[1]: # -32~-28 have mutation
    print('-32~-28 mutation')
else: 
    p_32_QV=phred33ToQ(k[p_32_position[0]])
    n=p_32_position[0]
    p_31_position=n+1
    p_30_position=n+2
    p_29_position=n+3
    p_28_position=n+4
    p_31_QV=phred33ToQ(k[p_31_position])
    p_30_QV=phred33ToQ(k[p_30_position])
    p_29_QV=phred33ToQ(k[p_29_position])
    p_28_QV=phred33ToQ(k[p_28_position])
    dict_1={p_32_QV:'-32',p_31_QV:'-31',p_30_QV:'-30',p_29_QV:'-29',p_28_QV:'-28'}
    for base in dict_1:
        if base < 0:
            print(dict_1[base],'heterozygous')
        else:
            print(dict_1[base],'WT')

p_cap_1 = 'ACATTT'
p_bm_cap_1 = BoyerMoore(p_cap_1, alphabet='ACGT')
cap_1_position=boyer_moore(p_cap_1, p_bm_cap_1, t)           
if cap_1_position+[1]==[1]:
    print('cap+1 mutation')
elif phred33ToQ(k[cap_1_position[0]]) < 0:
    print('cap+1 heterozygous')
else:
    print('cap+1 WT')
    
p_43 = 'AAACAGACACC'
p_bm_43 = BoyerMoore(p_43, alphabet='ACGT')
p_43_position=boyer_moore(p_43, p_bm_43, t)           
if p_43_position+[1]==[1]: 
    print('CAP+43~+40 mutation')
else: 
    p_43_QV=phred33ToQ(k[p_43_position[0]])
    a=p_43_position[0]
    p_42_position=a+1
    p_41_position=a+2
    p_40_position=a+3
    p_42_QV=phred33ToQ(k[p_42_position])
    p_41_QV=phred33ToQ(k[p_41_position])
    p_40_QV=phred33ToQ(k[p_40_position])
    list_1=[p_43_QV,p_42_QV,p_41_QV,p_40_QV]
    if min(list_1) > 0:
        print('CAP+43~+40','WT')
    else:
        print('CAP+43~+40','other mutant')
        
p_InitCD = 'TGGTGCA'
p_bm_InitCD = BoyerMoore(p_InitCD, alphabet='ACGT')
InitCD_position=boyer_moore(p_InitCD, p_bm_InitCD, t)           
if InitCD_position+[1]==[1]:
    print('InitCD mutation')
elif phred33ToQ(k[InitCD_position[0]]) < 0:
    print('InitCD heterozygous')
else:
    print('InitCD WT')
    
p_CD14 = 'GTGGGGC'
p_bm_CD14 = BoyerMoore(p_CD14, alphabet='ACGT')
CD14_position=boyer_moore(p_CD14, p_bm_CD14, t)
if CD14_position+[1]==[1]: 
    print('CD14/15 CD15/16 mutation')
else: 
    CD14_QV=phred33ToQ(k[CD14_position[0]])
    b=CD14_position[0]
    CD15_position=b+1
    CD1516_position=b+3
    CD16_position=b+4
    CD15_QV=phred33ToQ(k[CD15_position])
    CD1516_QV=phred33ToQ(k[CD1516_position])
    CD16_QV=phred33ToQ(k[CD16_position])
    list_2=[CD14_QV,CD15_QV]
    list_3=[CD15_QV,CD16_QV]
    if min(list_2) > 0:
        print('CD14/15','WT')
    else:
        print('CD14/15','other mutant')
    if min(list_3)>0:
        print('CD15/16','WT')
    else:
        print('CD15/16','other mutant')
        
p_CD17 = 'AAGGTGA'
p_bm_CD17 = BoyerMoore(p_CD17, alphabet='ACGT')
CD17_position=boyer_moore(p_CD17, p_bm_CD17, t)           
if CD17_position+[1]==[1]:
    print('CD17 mutation')
elif phred33ToQ(k[CD17_position[0]]) < 0:
    print('CD17 heterozygous')
else:
    print('CD17 WT')
    
p_CD26 = 'GTGGGGC'
p_bm_CD26 = BoyerMoore(p_CD26, alphabet='ACGT')
CD26_position=boyer_moore(p_CD26, p_bm_CD26, t)
if CD26_position+[1]==[1]: 
    print('CD26 mutation')
elif phred33ToQ(k[CD26_position[0]]) < 0:
    print('CD26 heterozygous')
else:
    print('CD26 WT')
if CD26_position+[1]!=[1]:
    c=CD26_position[0]
    CD27_position=c+5
    CD28_position=c+6
    CD27_QV=phred33ToQ(k[CD27_position])
    CD28_QV=phred33ToQ(k[CD28_position])
    list_4=[CD27_QV,CD28_QV]
    if min(list_4) > 0:
        print('CD27/28','WT')
    else:
        print('CD27/28','other mutant')

p_IVS_I2 = 'AGGTTGGT'
p_bm_IVS_I2 = BoyerMoore(p_IVS_I2, alphabet='ACGT')
IVS_I2_position=boyer_moore(p_IVS_I2, p_bm_IVS_I2, t)
if IVS_I2_position+[1]==[1]: 
    print('IVS-I_-2 mutation')
else: 
    IVS_I2_QV=phred33ToQ(k[IVS_I2_position[0]])
    d=IVS_I2_position[0]
    IVS_I1_position=b+2
    IVS_I5_position=b+6
    IVS_I1_QV=phred33ToQ(k[IVS_I1_position])
    IVS_I5_QV=phred33ToQ(k[IVS_I5_position])
    dict_2={IVS_I2_QV:'IVS-I_-2',IVS_I1_QV:'IVS-I-1',IVS_I5_QV:'IVS-I-5'} 
    for base in dict_2:
        if base < 0:
            print(dict_2[base],'heterozygous')
        else:
            print(dict_2[base],'WT')
        
p_CD31 = 'CTGCTGGT'
p_bm_CD31 = BoyerMoore(p_CD31, alphabet='ACGT')
CD31_position=boyer_moore(p_CD31, p_bm_CD31, t)
if CD31_position+[1]==[1]: 
    print('CD31 mutation')
elif phred33ToQ(k[CD31_position[0]]) > 0:
    print('CD31 WT')
else:
    print('CD31 other mutant')
    
p_CD37 = 'GACCCA'
p_bm_CD37 = BoyerMoore(p_CD37, alphabet='ACGT')
CD37_position=boyer_moore(p_CD37, p_bm_CD37, t)
if CD37_position+[1]==[1]: 
    print('CD37 mutation')
elif phred33ToQ(k[CD37_position[0]]) < 0:
    print('CD37 heterozygous')
else:
    print('CD37 WT')

p_CD38 = 'ACCCA'
p_bm_CD38 = BoyerMoore(p_CD38, alphabet='ACGT')
CD38_position=boyer_moore(p_CD38, p_bm_CD38, t)
if CD38_position+[1]==[1]: 
    print('CD38 mutation')
elif phred33ToQ(k[CD38_position[0]]) < 0:
    print('CD38 heterozygous')
else:
    print('CD38 WT')

