import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        if not isinstance(fact_or_rule, Fact) and not isinstance(fact_or_rule, Rule):
            return None

        if isinstance(fact_or_rule, Fact):
            fact_retract = self._get_fact(fact_or_rule)
            if fact_retract.asserted and fact_retract.supported_by:
                return None
            if not fact_retract.supported_by:
                # remove fact_retract from supported_by of other facts 
                for f_sup in fact_retract.supports_facts:
                    for fr in f_sup.supported_by:
                        if fact_retract in fr:
                            real_r = self._get_rule(fr[1])
                            real_r.supports_facts.remove(f_sup)
                            real_f_sup = self._get_fact(f_sup)
                            real_f_sup.supported_by.remove(fr)
                        if not real_f_sup.supported_by:
                            self.kb_retract(real_f_sup)
                # remove fact_retract from supported_by of other rules
                for r_sup in fact_retract.supports_rules:
                    for fr in r_sup.supported_by:
                        if fact_retract in fr:
                            real_r = self._get_rule(fr[1])
                            real_r.supports_rules.remove(r_sup)
                            real_r_sup = self._get_rule(r_sup)
                            real_r_sup.supported_by.remove(fr)
                        if not real_r_sup.asserted:
                            self.kb_retract(real_r_sup)
                self.facts.remove(fact_retract)
                
        if isinstance(fact_or_rule, Rule):
            if fact_or_rule.asserted:
                return None
            else:
                rule_retract = self._get_rule(fact_or_rule)
                if not rule_retract.supported_by:
                    # remove rule_retract from supported_by of other facts 
                    for f_sup in rule_retract.supports_facts:
                        for fr in f_sup.supported_by:
                            if rule_retract in fr:
                                real_f = self._get_fact(fr[0])
                                real_f.supports_facts.remove(f_sup)
                                real_f_sup = self._get_fact(f_sup)
                                real_f_sup.supported_by.remove(fr)
                            if not real_f_sup.supported_by:
                                self.kb_retract(real_f_sup)
                    # remove rule_retract from supported_by of other rules
                    for r_sup in rule_retract.supports_rules:
                        for fr in r_sup.supported_by:
                            if rule_retract in fr:
                                real_f = self._get_fact(fr[0])
                                real_f.supports_facts.remove(r_sup)
                                real_r_sup = self._get_rule(r_sup)
                                real_r_sup.supported_by.remove(fr)
                            if not real_r_sup.asserted:
                                self.kb_retract(real_r_sup)
                    self.rules.remove(rule_retract)
                

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        
        ####################################################
        # Student code goes here
        # match to first lhs statement
        bindings_match = match(fact.statement, rule.lhs[0])

        if bindings_match:
            # If there is more than 1 statement in the lhs of rule
            lhs_instantiated = []
            rhs_instantiated = instantiate(rule.rhs, bindings_match)
            if (len(rule.lhs) > 1):
                for statement in rule.lhs[1:]:
                    # instantiate makes a new statement 
                    # (either lhs or rhs) of rule with variable bindings
                    lhs_instantiated.append(instantiate(statement, bindings_match))
                
            # create new fact if there's only 1 lhs statement 
            if not len(lhs_instantiated):    
                fact_inferred = Fact(rhs_instantiated, supported_by=[[fact, rule]])
                rule.supports_facts.append(fact_inferred)
                fact.supports_facts.append(fact_inferred)    
                kb.kb_assert(fact_inferred)
            # create new rule if more than 1 lhs statement    
            else:    
                rule_inferred = Rule([lhs_instantiated, rhs_instantiated], supported_by=[[fact, rule]])
                rule.supports_rules.append(rule_inferred)
                fact.supports_rules.append(rule_inferred)    
                kb.kb_assert(rule_inferred)