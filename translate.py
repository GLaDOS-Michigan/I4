# Haojun Ma(mahaojun@umich.edu)

import ivy_init
#import ivy_interp as itp
import ivy_actions as act
import ivy_utils as utl
#import ivy_logic_utils as lut
#import ivy_logic as lg
import ivy_utils as iu
import ivy_module as im
#import ivy_alpha
#import ivy_art
#import ivy_interp
#import ivy_compiler
#import ivy_isolate
import ivy_ast
#import ivy_theory as ith
#import ivy_transrel as itr
#import ivy_solver as islv
#import ivy_fragment as ifc
from ivy_compiler import read_module
import sys
import math

def usage():
    print "usage: \n  {} file.ivy".format(sys.argv[0])
    sys.exit(1)

def f_ConstantSort(x):
    assert isinstance(x, ivy_ast.ConstantSort)
    return ' is just a sort'

def f_Variable(x):
    assert isinstance(x, ivy_ast.Variable)
    assert x.args == []
    return x.rep + ':' + x.sort

def f_Atom(x):
    assert isinstance(x, ivy_ast.Atom)
    ret = x.rep
    if x.args:
        ret += '(' + ', '.join([astdict[type(i)](i) for i in x.args]) + ')'
    return ret

def inst_Assign(x, modefies):
    assert isinstance(x, act.AssignAction)
    assert len(x.args) == 2
    assert isinstance(x.args[0], ivy_ast.App)
    ret = []
    name = x.args[0].rep
#    val = astdict[type(x.args[1])](x.args[1], dict())
    modefies.add(name)
    instlist = [(name, ['(= bv_true bv_true)'], dict())]
    args = map(lambda x: astdict[type(x)](x, dict()), x.args[0].args)
    if name in constants:
        for c, a in zip(constants[name], args):
            newlist = []
            for i in range(instance[c]):
                for l in instlist:
                    newdic = dict(l[2])
                    if a.isupper():
                        newdic[a] = (c, i)
                        newlist.append(('%s_%d' % (l[0], i), l[1], newdic))
                    else:
                        newlist.append(('%s_%d' % (l[0], i), l[1] + ['(= %s %s%d)' % (a, c, i)], newdic))
            instlist = newlist

        for inst in instlist:
            ret.append('(update_%s %s_next %s (and %s) %s)' % (name, inst[0], inst[0], ' '.join(inst[1]), astdict[type(x.args[1])](x.args[1], inst[2])))
    else:
        ret.append('(= %s_next %s)' % (name, astdict[type(x.args[1])](x.args[1], dict())))
    return ret

def inst_copy(name):
    assert name in constants
    instlist = [name]
    for c in constants[name]:
        newlist = []
        for i in range(instance[c]):
            newlist += map(lambda st: '%s_%d' % (st, i), instlist)
        instlist = newlist
    return map(lambda st: '(= %s %s_next)' % (st, st), instlist)
            
def f_AssignAction(x, modefies):
    ret = inst_Assign(x, modefies)
    return '(and %s)' % ' '.join(ret)

def f_RequiresAction(x, modefies):
    assert isinstance(x, act.RequiresAction)
    assert len(x.args) == 1
#    print 'assert', type(x.args[0])
#    f_Atom(x.args[0])
    return instantiate(x.args[0])

def f_Implies(x):
    assert isinstance(x, ivy_ast.Implies)
    assert len(x.args) == 2
    return astdict[type(x.args[0])](x.args[0]) + ' -> ' + astdict[type(x.args[1])](x.args[1])

def f_LabeledFormula(x):
    assert isinstance(x, ivy_ast.LabeledFormula)
    assert len(x.args) == 2
#    print type(x.formula)
    return '[' + x.name + '] ' + astdict[type(x.formula)](x.formula)

def f_Sequence(x, modefies):
    assert isinstance(x, act.Sequence)
    return '(and ' + ' '.join([actiondict[type(i)](i, modefies) for i in x.args]) + ')'

def declare_paras(prefix, paras):
    for para in paras:
        para.rep = para.rep.replace(':', '_')
    return '\n'.join(map(lambda para: '(declare-fun %s_%s () %s_type)' % (prefix, para.rep, para.sort), paras))

def f_ActionDef(x):
    assert isinstance(x, ivy_ast.ActionDef)
    assert len(x.args) == 2
#    print len(x.args), type(x.args[0]), type(x.args[1])
#    print len(x.args[1].args)
#    print type(x.args[0]), type(x.formal_params), type(x.formal_returns)
#    for param in x.formal_params:
#        print type(param)
#    if x.formal_params:
#        print type(x.formal_params[0])
    modefies[x.args[0].rep] = set()
    para = ' '.join(map(lambda para: "(%s %s_type)" % (para.rep, para.sort), x.formal_params))
    lemma = ' '.join(map(lambda para: "(is_%s %s)" % (para.sort, para.rep), x.formal_params))
    return "\n(define-fun %s_fun (%s) Bool (and %s %s))" % (x.args[0].rep, para, lemma, actiondict[type(x.args[1])](x.args[1], modefies[x.args[0].rep]))

def f_IfAction(x, modefies):
    assert isinstance(x, act.IfAction)
    cond = instantiate(x.args[0])
    thens = x.args[1].args
    ret = []
    if len(x.args) > 3:
        elses = x.args[2].args
    else:
        elses = []
    for c1 in thens:
        assert isinstance(c1, act.AssignAction)
        name = c1.args[0].rep
        th = inst_Assign(c1, modefies)
        el = inst_copy(name)
        for c2 in elses:
            if c2.args[0].rep == name:
                el = inst_Assign(c2, modefies)
                break
        ret.append('(and %s)' % (' '.join(map(lambda x: '(ite %s %s %s)' % (cond, x[0], x[1]), zip(th, el)))))
    for c2 in elses:
        assert isinstance(c1, act.AssignAction)
        name = c2.args[0].rep
        flag = True
        el = inst_Assign(c2, modefies)
        for c1 in thens:
            if c1.args[0].rep == name:
                flag = False
                break
        if flag:
            ret.append('(and %s)' % (' '.join(map(lambda x: '(ite %s %s %s)' % (cond, x[0], x[1]), zip(inst_copy(name), el)))))
    return '(and %s)' % ' '.join(ret)

def f_ActionDecl(x):
    assert isinstance(x, ivy_ast.ActionDecl)
    assert len(x.args) == 1
    assert x.attributes == ()
    return f_ActionDef(x.args[0]).replace(':', '_')

def f_MixinDecl(x):
    assert isinstance(x, ivy_ast.MixinDecl)
    return '''I don't know what's MixinDecl'''

def f_TypeDef(x):
    assert isinstance(x, ivy_ast.TypeDef)
    assert len(x.args) == 2
    return f_Atom(x.args[0])

def f_TypeDecl(x):
    assert isinstance(x, ivy_ast.TypeDecl)
    assert x.attributes == ()
    assert len(x.args) == 1
    return f_TypeDef(x.args[0])

def f_ConstantDecl(x):
    assert isinstance(x, ivy_ast.ConstantDecl)
    assert len(x.args) == 1
    assert x.attributes == ()
    return 'individual ' + f_Atom(x.args[0])

def f_ExportDef(x):
#not dealing with scope
    assert isinstance(x, ivy_ast.ExportDef)
    assert len(x.args) == 2
    return f_Atom(x.args[0])

def f_ExportDecl(x):
    assert isinstance(x, ivy_ast.ExportDecl)
    assert len(x.args) == 1
    assert x.attributes == ()
    return 'export ' + f_ExportDef(x.args[0])

def f_ConjectureDecl(x):
    assert isinstance(x, ivy_ast.ConjectureDecl)
    assert x.attributes == ()
    assert len(x.args) == 1
    return 'assert ' + f_LabeledFormula(x.args[0])

#astdict[ivy_ast.App] = f_App
#astdict[ivy_ast.Atom] = f_Atom
#astdict[ivy_ast.Variable] = f_Variable
#astdict[ivy_ast.MixinDecl] = f_MixinDecl
#astdict[ivy_ast.TypeDecl] = f_TypeDecl
#astdict[ivy_ast.ConstantDecl] = f_ConstantDecl
#astdict[ivy_ast.ExportDecl] = f_ExportDecl
#astdict[ivy_ast.ConjectureDecl] = f_ConjectureDecl
#astdict[ivy_ast.Forall] = f_Forall
#astdict[ivy_ast.Implies] = f_Implies

actiondict = dict()
actiondict[act.AssignAction] = f_AssignAction
actiondict[act.RequiresAction] = f_RequiresAction
actiondict[act.IfAction] = f_IfAction
actiondict[act.Sequence] = f_Sequence

constants = dict()
modefies = dict()
#def argsmap(args):
#    ret = ''
#    print type(args[0])
#    for item in map(lambda x: astdict[type(x)](x), args):
#        ret = reduce(lambda x, y: x + y, map(lambda st: [st + ' (= ' + it + ' bv_true)' for it in item], ret))
#    return ret

def make_type(x, paratype):
    assert isinstance(x, ivy_ast.Atom)
    if hasattr(x,'sort'):
        ret = x.sort + '_type'
    else:
        ret = 'bool_type'
    names = [x.rep]
    for para in x.args:
        newnames = []
        for i in range(instance[para.sort]):
            newnames += map(lambda st: '%s_%d' % (st, i), names)
        names = newnames
        paratype.append(para.sort)
    for name in names:
        print '''(declare-fun %s () %s)\n(declare-fun %s_next () %s)\n(define-fun .%s () %s (! %s :next %s_next))''' % (name, ret, name, ret, name, ret, name, name)
        if ret != 'bool_type':
            lemmas.append('(is_%s %s)' % (x.sort, name))
    print '''(define-fun update_%s ((newv %s) (prev %s) (cond Bool) (val %s)) Bool (= newv (ite cond val prev)))''' % (x.rep, ret, ret, ret)
#    print '''(define-fun copy_%s ((newv %s) (prev %s)) Bool (= prev newv))''' % (x.rep, ret, ret)

def type_infer(x):
    foralldict = dict()
    existdict = dict()
    if isinstance(x, ivy_ast.Atom) or isinstance(x, ivy_ast.App):
        if x.rep == '=':
            for arg in x.args:
                retdict1, retdict2 = type_infer(arg)
                foralldict.update(retdict1)
                existdict.update(retdict2)    
            return foralldict, existdict
        name = x.rep
        if name not in constants:
            return foralldict, existdict
        for i in range(len(constants[name])):
            if isinstance(x.args[i], ivy_ast.Variable) or isinstance(x.args[i], ivy_ast.App):
                if x.args[i].rep[0].isupper():
                    if x.args[i].rep not in foralldict and x.args[i].rep not in existdict:
                        foralldict[x.args[i].rep] = constants[name][i]
                    x.args[i].sort = constants[name][i]
            else:
                print type(x.args[i]), 'is not finished'
    else:
         for arg in x.args:
            retdict1, retdict2 = type_infer(arg)
            foralldict.update(retdict1)
            existdict.update(retdict2)
    if isinstance(x, ivy_ast.Exists):
        for var in x.bounds:
            if var.rep in foralldict:
                existdict[var.rep] = foralldict[var.rep]
                del foralldict[var.rep]
    return foralldict, existdict

def instantiate_And(x, dic):
    assert isinstance(x, ivy_ast.And)
#    print 'and', type(x.args), x.args, dir(x.args)
    if len(x.args) == 0:
        return 'bv_true'
    else:
        return '(ite (and ' + ' '.join(map(lambda arg: '(= %s bv_true)' % astdict[type(arg)](arg, dic), x.args)) + ') bv_true bv_false)'

def instantiate_Or(x, dic):
    assert isinstance(x, ivy_ast.Or)
#    print 'or', type(x.args), x.args, dir(x.args)
    if len(x.args) == 0:
        return 'bv_false'
    else:
        return '(ite (or ' + ' '.join(map(lambda arg: '(= %s bv_true)' % astdict[type(arg)](arg, dic), x.args)) + ') bv_true bv_false)'

def instantiate_Not(x, dic):
    assert isinstance(x, ivy_ast.Not)
    return '(ite (= %s bv_true) bv_false bv_true)' % astdict[type(x.args[0])](x.args[0], dic)

def instantiate_Variable(x, dic):
    assert isinstance(x, ivy_ast.Variable)
    if x.rep in dic:
        return '%s%d' % (dic[x.rep][0], dic[x.rep][1])
    else:
        return x.rep

def instantiate_Atom(x, dic):
    assert isinstance(x, ivy_ast.Atom)
    name = x.rep
    if name == '=':
#        print "I don't know why they use Atom for euqal"
        return '(ite (= ' + ' '.join(map(lambda arg: astdict[type(arg)](arg, dic), x.args)) + ') bv_true bv_false)'
#    if name == 'le':
#        return '(ite (bvule %s %s) bv_true bv_false)' % (astdict[type(x.args[0])](x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic))
#        return '(ite (<= %s %s) bv_true bv_false)' % (astdict[type(x.args[0])](x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic))
    if name not in constants:
        return name
    args = [[]]
    for i in range(len(constants[name])):
        if x.args[i].rep in dic:
            args = map(lambda a: a + [(None, dic[x.args[i].rep][1])], args)
        else:
            newargs = []
            st = astdict[type(x.args[i])](x.args[i], dic)
            for j in range(instance[constants[name][i]]):
                newargs += map(lambda x: x + [(st, j)], args)
            args = newargs
    ret = ''
    for arg in args:
        st = x.rep
        cond = []
        for i in range(len(constants[name])):
            st = '%s_%d' % (st, arg[i][1])
            if arg[i][0]:
                cond.append('(= %s %s%d)' % (arg[i][0], constants[name][i], arg[i][1]))
        if cond:
            if arg != args[-1]:
                ret = '%s(ite (and %s) %s ' % (ret, ' '.join(cond), st)
            else:
                ret = '%s%s' % (ret, st) + ')' * (len(args) - 1)
        else:
            ret = st
    return ret

def instantiate_App(x, dic):
    assert isinstance(x, ivy_ast.App)
    name = x.rep
    ret = name
    if name == '=':
        print "I don't know why they use App for euqal"
    if name not in constants:
        return name
    args = [[]]
    for i in range(len(constants[name])):
        if x.args[i].rep in dic:
            args = map(lambda a: a + [(None, dic[x.args[i].rep][1])], args)
        else:
            newargs = []
            st = astdict[type(x.args[i])](x.args[i], dic)
            for j in range(instance[constants[name][i]]):
                newargs += map(lambda x: x + [(st, j)], args)
            args = newargs
    ret = ''
    for arg in args:
        st = x.rep
        cond = []
        for i in range(len(constants[name])):
            st = '%s_%d' % (st, arg[i][1])
            if arg[i][0]:
                cond.append('(= %s %s%d)' % (arg[i][0], constants[name][i], arg[i][1]))
        if cond:
            if arg != args[-1]:
                ret = '%s(ite (and %s) %s ' % (ret, ' '.join(cond), st)
            else:
                ret = '%s%s' % (ret, st) + ')' * (len(args) - 1)
        else:
            ret = st
    return ret

def instantiate_Assign(x, dic):
    assert isinstance(x, act.AssignAction)
    return '(ite (= %s %s) bv_true bv_false)' % (instantiate_App(x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic))

def same_assign(x, y, st):
    assert isinstance(x, act.AssignAction)
    assert isinstance(y, act.AssignAction)
    return st != '' and x.args[0].rep == y.args[0].rep

def instantiate_Implies(x, dic):
    assert isinstance(x, ivy_ast.Implies)
    return '(ite (=> (= %s bv_true) (= %s bv_true)) bv_true bv_false)' % (astdict[type(x.args[0])](x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic))

def instantiate_Forall(x, dic):
    assert isinstance(x, ivy_ast.Forall)
    return astdict[type(x.args[0])](x.args[0], dic)

def instantiate_Exists(x, dic):
    assert isinstance(x, ivy_ast.Exists)
    return astdict[type(x.args[0])](x.args[0], dic)

class conditionalexp(ivy_ast.Formula):
    def __repr__(self):
        return repr(self.args[0]) + '?' + repr(self.args[1]) + ':' + repr(self.args[2])

def instantiate_conditionalexp(x, dic):
    assert isinstance(x, conditionalexp)
    return '(ite (= %s bv_true) (ite (= %s %s) bv_true bv_false) (ite (= %s %s) bv_true bv_false))' % (astdict[type(x.args[0])](x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic), astdict[type(x.args[2])](x.args[2], dic), astdict[type(x.args[1])](x.args[1], dic), astdict[type(x.args[3])](x.args[3], dic))

def instantiate_Ite(x, dic):
    assert isinstance(x, ivy_ast.Ite)
    return '(ite (= %s bv_true) %s %s)' % (astdict[type(x.args[0])](x.args[0], dic), astdict[type(x.args[1])](x.args[1], dic), astdict[type(x.args[2])](x.args[2], dic))

astdict = dict()
#astdict[ivy_ast.ActionDecl] = f_ActionDecl
astdict[ivy_ast.And] = instantiate_And
astdict[ivy_ast.Or] = instantiate_Or
astdict[ivy_ast.Not] = instantiate_Not
astdict[ivy_ast.Variable] = instantiate_Variable
astdict[ivy_ast.App] = instantiate_App
astdict[ivy_ast.Atom] = instantiate_Atom
astdict[ivy_ast.Implies] = instantiate_Implies
astdict[ivy_ast.Exists] = instantiate_Exists
astdict[ivy_ast.Forall] = instantiate_Forall
astdict[ivy_ast.Ite] = instantiate_Ite
astdict[act.AssignAction] = instantiate_Assign
astdict[conditionalexp] = instantiate_conditionalexp

def instantiate(x):
    foralldict, existdict = type_infer(x)
    foralllist = [dict()]
    existlist = [dict()]
    for var, typ in foralldict.iteritems():
        newlist = []
        for d in foralllist:
            for i in range(instance[typ]):
                dd = dict(d)
                dd[var] = (typ, i)
                newlist.append(dd)
        foralllist = newlist
    for var, typ in existdict.iteritems():
        newlist = []
        for d in existlist:
            for i in range(instance[typ]):
                dd = dict(d)
                dd[var] = (typ, i)
                newlist.append(dd)
        existlist = newlist
#    print len(dictlist)
    ret = []
    for d1 in foralllist:
        st = '(or'
        for d2 in existlist:
            dd = dict(d1)
            dd.update(d2)
            st += ' (= %s bv_true)' % (astdict[type(x)](x, dd))
        ret.append(st + ')')
#    print ret
    return '(and ' + ' '.join(ret) + ')'


def change(x, y):
    x = conditionalexp(ivy_ast.Atom('=', x.args[0].args[0], y.args[0].args[0]), x.args[0], y.args[1], x.args[1])
    return instantiate(x)

def generate_trans(actions):
    act = ''
    fun = ''
    for action in actions:
        name = action.args[0].rep
        if len(action.formal_params) > 0:
            fun += '(=> (= action %s) (and (%s_fun %s)' % (name, name, ' '.join(map(lambda para: '%s_%s' % (name, para.rep), action.formal_params)))
        else:
            fun += '(=> (= action %s) (and %s_fun' % (name, name)

        for cons in constants:
            if cons not in modefies[name]:
                fun += ' ' + ' '.join(inst_copy(cons))
        fun += ')) '

    fun += '(=> (not (or %s)) (and %s))' % (' '.join(map(lambda action: '(= action %s)' % (action.args[0].rep), actions)), ' '.join(map(lambda const: ' '.join(inst_copy(const)), constants.keys())))
    return '(define-fun .trans () Bool (! (and %s %s %s) :trans true))\n' % (act, fun, ' '.join(lemmas))

typelength = set([0, 1])

def translate(decls):
    print '''
(set-info :source |Haojun Ma (mahaojun@umich.edu)|)

; Typecast bit to bool
(define-sort bool_type () (_ BitVec 1))
(define-fun bv_false () bool_type (_ bv0 1))
(define-fun bv_true  () bool_type (_ bv1 1))
(define-fun is_bool ((x bool_type)) Bool (or (= x bv_true) (= x bv_false)))
'''

    print '''; Define and enumerate transition system parameters'''
    for decl in decls.decls:
        if type(decl) == ivy_ast.TypeDecl:
            name = f_TypeDecl(decl)
#            if name == 'epoch' or name == 'round':
#                print '''(define-sort %s_type () Int)''' % (name)
#                for i in range(instance[name]):
#                    print '''(define-fun %s%d () %s_type %d)''' % (name, i, name, i)
#                    print '''(declare-fun %s%d_next () %s_type)''' % (name, i, name)
#                    print '''(define-fun .%s%d () %s_type (! %s%d :next %s%d_next))''' % (name, i, name, name, i, name, i)
#            else:
            if True:
                l = math.ceil(math.log(instance[name], 2))
                while l in typelength:
                    l += 1
                typelength.add(l)
                print '''(define-sort %s_type () (_ BitVec %d))''' % (name, l)
                for i in range(instance[name]):
                    print '''(define-fun %s%d () %s_type (_ bv%d %d))''' % (name, i, name, i, l)
#                    print '''(declare-fun %s%d () %s_type)''' % (name, i, name)
#                    print '''(declare-fun %s%d_next () %s_type)''' % (name, i, name)
#                    print '''(define-fun .%s%d () %s_type (! %s%d :next %s%d_next))''' % (name, i, name, name, i, name, i)
            print '''(define-fun is_%s ((%s %s_type)) Bool (or %s))''' % (name, name, name, ' '.join(map(lambda i: '(= %s %s%d)' % (name, name, i), range(instance[name]))))
#            distinct = ''
#            for i in range(instance[name]):
#                for j in range(i):
#                    distinct += ' (= %s%d %s%d)' % (name, j, name, i)
#            print '''(define-fun lemma_%s () Bool (and %s (not (or%s))))''' % (name, ' '.join(map(lambda i: '(= %s%d %s%d_next)' % (name, i, name, i), range(instance[name]))), distinct)
#            lemmas.append('lemma_%s' % name)

    print '''\n; Declare transition system states'''
    for decl in decls.decls:
        if type(decl) == ivy_ast.ConstantDecl:
            if isinstance(decl.args[0], ivy_ast.Atom):
                name = decl.args[0].rep
                constants[name] = []
                make_type(decl.args[0], constants[name])
            else:
                cons = decl.args[0]
                print '''(declare-fun %s () %s_type)''' % (cons.rep, cons.sort)
                print '''(declare-fun %s_next () %s_type)''' % (cons.rep, cons.sort)
                print '''(define-fun .%s () %s_type (! %s :next %s_next))''' % (cons.rep, cons.sort, cons.rep, cons.rep)
                lemmas.append('(is_%s %s)' % (cons.sort, cons.rep))
                lemmas.append('(= %s_next %s)' % (cons.rep, cons.rep))
                if 'transaction' not in instance:
                    if cons.rep == 'zero' or cons.rep == 'org':
                        lemmas.append('(= %s %s%d)' % (cons.rep, cons.sort, 0))
#                if cons.rep == 'e':
#                    pass
#                    lemmas.append('(= %s %s%d)' % (cons.rep, cons.sort, 1))
#                elif cons.rep == 'maxint':
#                    pass
#                    lemmas.append('(= %s %s%d)' % (cons.rep, cons.sort, instance[cons.sort] - 1))
#                elif cons.rep == 'other':
#                    pass
#                else:
#                    lemmas.append('(= %s %s%d)' % (cons.rep, cons.sort, 0))
        elif type(decl) == ivy_ast.AxiomDecl:
            print '''(define-fun axiom_%s () Bool %s)''' % (decl.args[0].name, instantiate(decl.args[0].formula))
            lemmas.append('axiom_%s' % decl.args[0].name)

    for decl in decls.decls:
        if type(decl) == ivy_ast.ActionDecl:
            if f_Atom(decl.args[0].args[0]).startswith('init'):
                print '''\n; Initial state'''
                inits = []
                for i, arg in enumerate(decl.args[0].args[1].args):
                    inits.append(instantiate(arg))
                    for j in range(i):
                        if same_assign(arg, decl.args[0].args[1].args[j], inits[j]):
                            inits[j] = change(decl.args[0].args[1].args[j], arg)
                            inits[i] = ''
                print '''(define-fun .init () Bool (! (and %s) :init true))''' % (' '.join(inits))
            else:
                print f_ActionDecl(decl)
            print

    if 'epoch' in instance:
        pass
#        for i in range(instance['epoch']):
#            for j in range(instance['epoch']):
#                lemmas.append('(= le_%d_%d bv_%s)' % (i, j, 'true' if i <= j else 'false'))
    elif 'round' in instance:
        for i in range(instance['round']):
            for j in range(instance['round']):
                lemmas.append('(= le_%d_%d bv_%s)' % (i, j, 'true' if i <= j else 'false'))
#        for i in range(instance['acceptor']):
#            for j in range(instance['quorum']):
#                lemmas.append('(= member_%d_%d bv_%s)' % (i, j, 'true' if i != j else 'false'))
    elif 'term' in instance:
        for i in range(instance['term']):
            for j in range(instance['term']):
                lemmas.append('(= le_%d_%d bv_%s)' % (i, j, 'true' if i <= j else 'false'))
        for i in range(instance['node']):
            for j in range(instance['quorum']):
                lemmas.append('(= member_%d_%d bv_%s)' % (i, j, 'true' if i != j else 'false'))
    elif 'id' in instance:
        for i in range(instance['node']):
            lemmas.append('(= idn_%d id%d)' % (i, i)) 


    actions = []
    for decl in decls.decls:
        if type(decl) == ivy_ast.ExportDecl:
            for d in decls.decls:
                if type(d) == ivy_ast.ActionDecl and d.args[0].args[0].rep == decl.args[0].args[0].rep:
                    actions.append(d.args[0])
    l = math.ceil(math.log(len(actions) + 1, 2))
    while l in typelength:
        l += 1
    print '''; Declare actions'''
    print '''(define-sort action_type () (_ BitVec %d))''' % l
    print '\n'.join(map(lambda i: '(define-fun %s() action_type (_ bv%d %d))' % (actions[i].args[0].rep, i, l), range(len(actions))))
    print '''\n; Transition relation'''
    print '''(declare-fun action () action_type)'''
    for action in actions:
        print declare_paras(action.args[0].rep, action.formal_params)

    print generate_trans(actions)

    for decl in decls.decls:
        if type(decl) == ivy_ast.ConjectureDecl:
            print '''(define-fun .prop () Bool (! (and %s) :invar-property 0))''' % (instantiate(decl.args[0].formula))

instance = dict()
lemmas = []

def main():
    ivy_init.read_params()
    if not sys.argv[1].endswith('ivy'):
        usage()
    for i in range(2, len(sys.argv)):
        st = sys.argv[i].split('=')
        instance[st[0]] = eval(st[1])

    with im.Module():
        with utl.ErrorPrinter():
            with iu.SourceFile(sys.argv[1]):
                decls = read_module(ivy_init.open_read(sys.argv[1]))
                translate(decls)

if __name__ == "__main__":
    main()

