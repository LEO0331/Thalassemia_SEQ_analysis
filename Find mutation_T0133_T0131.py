#!/usr/bin/env python
# coding: utf-8

# In[1]:


import sys
get_ipython().system('{sys.executable} -m pip install ipython')


# In[2]:


import numpy as np


# In[3]:


def phred33ToQ (qual):
    return ord(qual)-33


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


# In[7]:


from Bio import SeqIO
handle = open("Desktop/TGB_work/seq_sets/BB1410016_ThaMuv7_T0133.ab1", "rb")
record=SeqIO.read(handle, "abi")
t = record.annotations['abif_raw']['PBAS2'] # sequences
n = record.annotations['abif_raw']['PCON2'] # qualities
p_CD41 = 'TTCTTTGAGTCCTTTG'
p_bm_CD41 = BoyerMoore(p_CD41, alphabet='ACGT')
CD41_position=boyer_moore(p_CD41, p_bm_CD41, t)           
if CD41_position+[1]==[1]: 
    print('CD41/42 mutation')
else: 
    CD41_QV=phred33ToQ(n[CD41_position[0]])
    a=CD41_position[0]
    CD41a_position=a+1
    CD42_position=a+2
    CD42a_position=a+3
    CD42b_position=a+4
    CD42c_position=a+5
    CD43_position=a+6
    CD41a_QV=phred33ToQ(n[CD41a_position])
    CD42_QV=phred33ToQ(n[CD42_position])
    CD42a_QV=phred33ToQ(n[CD42a_position])
    CD42b_QV=phred33ToQ(n[CD42b_position])
    CD42c_QV=phred33ToQ(n[CD42c_position])
    CD43_QV=phred33ToQ(n[CD43_position])
    list_1=[CD41_QV,CD41a_QV,CD42_QV,CD42a_QV,CD42b_QV,CD42c_QV]    
    if min(list_1) > -10:
        print('CD41/42','WT')
    else:
        print('CD41/42','other mutant')
    if CD43_QV > -10:
        print('CD43','WT')
    else:
        print('CD43','heterozygous')
         
p_CD71 = 'TAGTGAT'
p_bm_CD71 = BoyerMoore(p_CD71, alphabet='ACGT')
CD71_position=boyer_moore(p_CD71, p_bm_CD71, t)           
if CD71_position+[1]==[1]: 
    print('CD71/72','mutation')
else: 
    CD71_QV=phred33ToQ(n[CD71_position[0]])
    CD72_position=np.array(CD71_position)+[1]
    CD72_QV=phred33ToQ(n[CD72_position[0]])
    if CD71_QV > -10 and CD72_QV > -10:
        print('CD71/72','WT')
    else:
        print('CD71/72','other mutant')
        
p_IVS_II2 = 'TGAGTCTATGGGA'
p_bm_IVS_II2 = BoyerMoore(p_IVS_II2, alphabet='ACGT')
IVS_II2_position=boyer_moore(p_IVS_II2, p_bm_IVS_II2, t)           
if IVS_II2_position+[1]==[1]: 
    print('IVS_II-2','mutation')
else:
    IVS_II2_QV=phred33ToQ(n[IVS_II2_position[0]])
    IVS_II5_position=np.array(IVS_II2_position)+[3]
    IVS_II5_QV=phred33ToQ(n[IVS_II5_position[0]])
    if IVS_II2_QV > -10:
        print('IVS_II-2','WT')
    else:
        print('IVS_II-2','other mutant')
    if IVS_II5_QV < -10:
        print('IVS_II-5','heterozygous')
    else:
        print('IVS_II-5','WT')
        

