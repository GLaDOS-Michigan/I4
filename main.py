import sys
import subprocess
import os
from collections import defaultdict
from copy import copy
from itertools import permutations

numbers = set()
replace = {'!': '~', '&&': '&', '==': '='}
nameprefix = 'v'

for i in range(10):
    numbers.add(str(i))

def add_var(var, dic):
    l = len(var)
    while var[l - 1] in numbers and l > 0:
        l = l - 1
    if l == len(var) or l == 0:
        return var
    var = var.upper()
    if var not in dic[var[:l]]:
        dic[var[:l]].append(var)
    return '%s:%s'%(var, var[:l].lower())

def parse_var(st, used, config):
#    print 'parsing', st
    if st[0] == '_':
        st = st[1:]
    st = st.split('_')
    while len(st) > 1 and st[-2][-1] not in numbers:
        st[-2] = "%s_%s" % (st[-2], st[-1])
        st.pop()

    ret = st[-1]
    if ret != '<':
        if len(st) > 1:
            ret += '('
        else:
            # This is a constant. I need to remove its type in the beginning.
            l = -1
            for k in config.sorts:
                if ret.startswith(config.sorts[k].lower() + '_'):
                    l = max(l, len(config.sorts[k]))
            if ret.startswith('Boolean_'):
                l = max(l, len('Boolean'))
            assert '_' not in ret or l > 0, ret
            ret = ret[l + 1:]
            ret = add_var(ret, used)
        i = len(st) - 2
        while i >= 0:
            if i > 0:
                ret += add_var(st[i], used) + ', '
            else:
                ret += add_var(st[i], used) + ')'
            i = i - 1
#    print ret
        return ret
    else:
        return "%s < %s" % (add_var(st[1], used), add_var(st[0], used))

def parse(st, used, config):
    ret = ''
    l = 0
    while l < len(st):
        if st[l] == '?':
            print ret
            print st
            exit()
        if st[l] in ['(', ')', '~', ' ', '&', '=']:
            ret += st[l]
            l = l + 1
        elif st[l] == '\t':
            l = l + 1
        else:
            r = l + 1
            while st[r] not in ['(', ')', '~', ' ']:
                r = r + 1
            ret += parse_var(st[l:r], used, config)
            l = r
    return ret

def comp(dic1, dic2):
    for k in dic1:
        if k not in dic2:
            return False
        for v in dic1[k]:
            if v not in dic2[k]:
                return False
    return True

class Config():
    def __init__(self, fi):
        self.module = fi.readline().replace('\n', '')
        self.isolate = fi.readline().replace('\n', '').split('=')
        if 'isolate' == self.isolate[0]:
            self.isolate = self.isolate[1]
            assert fi.readline() == '\n'
        else:
            self.isolate = ''
        self.read_relations(fi)
        assert fi.readline() == '\n'
        self.read_sorts(fi)
        assert fi.readline() == '\n'
        self.read_prefix(fi)
#        assert fi.readline() == '\n'
#        self.read_insts(fi)

    def read_relations(self, fi):
        n = eval(fi.readline())
        self.relations = set()
        self.values = {}
        self.paras = {}
        for i in range(n):
            st = fi.readline().split()
            self.relations.add(st[2])
            self.values[st[2]] = st[1]
            self.paras[st[2]] = st[3:]

    def read_sorts(self, fi):
        n = eval(fi.readline())
        self.sorts = {}
        for i in range(n):
            st = fi.readline().split()
            self.sorts["%s'd" % st[1]] = st[0]

    def read_prefix(self, fi):
        n = eval(fi.readline())
        self.prefix = {}
        for i in range(n):
            st = fi.readline()[:-1].split('=')
            used = defaultdict(list)
            if (len(st) > 1):
                ret = "%s=%s" % (parse_var(st[0], used, self), parse_var(st[1], used, self))
            else:
                ret = "%s" % (parse_var(st[0], self.used, self))
            self.prefix[ret] = used
#        print self.prefix
    
class Invariant():
    def __init__(self, fi, config):
        self.invs = [] # list of generalized invariants
        self.vars = [] # list of dict (vartype, list of varname in this type).
        self.symmetry = set() # set of generalized invariants after applying symmetry. To remove the same invariant after quantifier.
        self.config = config
        for st in fi:
            if st != '\n' and st.find('sz:') == -1 and st.find('property') == -1:
                assert 'fml_' not in st and 'loc_' not in st
                st = st.replace('\n', '')
                self.parse(st, self.config)
        for i in range(len(self.invs)):
            prefix = []
            for p in config.prefix:
                if comp(config.prefix[p], self.vars[i]):
                    prefix.append(p)
            for t in self.vars[i]:
                for l in range(1, len(self.vars[i][t])):
                    for r in range(l):
                        prefix.append("%s ~= %s" % (self.vars[i][t][r], self.vars[i][t][l]))
            if prefix:
                self.invs[i] = "(%s) -> (%s)" % (' & '.join(prefix), self.invs[i])

    def __str__(self):
        ret = 'private {\n'
        for i in range(len(self.invs)):
            ret += "invariant [%s%d] %s\n" % (nameprefix, i, self.invs[i])
        ret += '}\n'
        return ret

    def parse(self, st, config):
        var = defaultdict(list)
        st = st.replace('___', '_')
        if config.isolate:
            st = st.replace('%s.' % (config.isolate), '')
        if st.endswith('&&'):
            st = st[:-2]
        for k in config.sorts:
            st = st.replace(k, config.sorts[k])
        for k in replace:
            st = st.replace(k, replace[k])
        result = parse(st, var, config)
        if self.check_symmetry(result, var):
            self.invs.append(result)
            self.vars.append(var)

    def check_symmetry(self, result, var):
        rep = [result]
        for typ in var:
            l = len(var[typ])
            newl = []
            for perm in permutations(range(l)):
                tmp = list(rep)
#                print 'before:', tmp
                for org, v in zip(var[typ], perm):
                    if not any(org in self.config.prefix[p][typ] for p in self.config.prefix):
#                    print 'replace %s %s_%d' % (org, typ, v)
                        tmp = map(lambda x: x.replace(org, '%s_%d' % (typ, v)), tmp)
#                print 'after:', tmp
                newl.extend(tmp)
            rep = newl
#        print '\n'.join(rep)
        assert len(set(rep)) == len(rep)
        for s in rep:
            if s in self.symmetry:
                return False
        self.symmetry = self.symmetry.union(rep)
        return True

    def remove(self, i):
        self.invs[i] = 'false -> (%s)' % self.invs[i]

def check(inv, config):
    fi = open('%s_%s.bak' % (config.module, config.isolate), 'r')
    fo = open('%s_%s.ivy' % (config.module, config.isolate), 'w')
    flag = True
    for st in fi:
        if 'invariant' in st and flag:
            fo.write(str(inv))
            flag = False
        fo.write(st)
    fo.close()
    fi.close()
    global cnt
    if cnt < 1:
        fi = open('log.txt', 'r')
    else:
        if config.isolate:
            output = subprocess.Popen("ivy_check isolate=%s %s_system.ivy | tee log.txt " % (config.isolate, config.module), shell=True, stdout=subprocess.PIPE)
        else:
            output = subprocess.Popen("ivy_check %s_.ivy | tee log.txt " % (config.module), shell=True, stdout=subprocess.PIPE)
        fi = iter(output.stdout.readline, '')

    for st in fi:
        if any(p in st for p in ['Initialization', '(internal)']):
            print 'starting' + st,
        if 'FAIL' in st and 'line' in st:
            print st,
            if config.isolate:
                st = st.replace('%s.%s' % (config.isolate, nameprefix), '')
            else:
                st = st.replace(': %s' % (nameprefix), ': ')
            p = st.find('line')
            p += st[p:].find(':') + 2
            r = st[p:].find(' ')
            fail = eval(st[p:p + r])
            if fail >= 1000000:
                print 'safety failed'
                exit()
            inv.remove(fail)
        if st == 'OK\n':
            return True
    return False

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print 'python main.py config inv_file'
        exit()
    config = Config(open(sys.argv[1], 'r'))
    inv = Invariant(open(sys.argv[2], 'r'), config)
    if not os.path.isfile('%s_%s.bak' % (config.module, config.isolate)):
        if config.isolate:
            os.system('cp %s_%s.ivy %s_%s.bak' % (config.module, config.isolate, config.module, config.isolate))
        else:
            os.system('cp %s.ivy %s_%s.bak' % (config.module, config.module, config.isolate))
    global cnt
    cnt = 1
    while not check(inv, config):
        print cnt, 'done'
        cnt += 1
        if cnt > 10:
            exit()
    print 'Success!'
