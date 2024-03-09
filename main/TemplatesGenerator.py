from collections import defaultdict
import json
import logging
import os
import sys
import pandas as pd
import importlib
from main.verbalizer.utilsFunctions import *
import re

verbalizer_path = os.path.abspath('main/verbalizer')
sys.path.append(verbalizer_path)
import ProgramVerbalizer
importlib.reload(ProgramVerbalizer)

import AggregateVerbalizer
importlib.reload(AggregateVerbalizer)

class TemplatesGenerator:
    
    logging.getLogger().setLevel(logging.INFO)

    def __list_duplicates(self, seq):
        tally = defaultdict(list)
        for i,item in enumerate(seq):
            tally[item].append(i)
        return ((key,locs) for key,locs in tally.items())

    def __split_branches_plan_step(self, join_step):
        check_list = list()
        join_step = [ele for ele in join_step if ele != '']
        for j in range(len(join_step)):
            if join_step[j][-1] != '.':
                join_step[j] = join_step[j] + '.'
        for j in range(len(join_step)):
            check_list.append(join_step[j].split('(')[0])
        index_duplicates = sorted(self.__list_duplicates(check_list))
        
        branches = list()
        fb = list()
        fb.append(branches.copy())

        for d in index_duplicates:
            if len(d[1]) == 1:
                for j in range(len(fb)):
                    fb[j].append(join_step[d[1][0]])
            else:
                for k in range(len(d[1])-1):
                    fb.append(fb[0].copy())
                for k in range(len(fb)):
                    fb[k].append(join_step[d[1][k]])

        return fb
    
    def __get_templates(self, plan_path):

        with open(plan_path) as c:
            # deserialize chase_file
            plan = json.load(c)

        # Clean plan and sources
        for i in range(len(plan)):
            plan[i]['sources'] = plan[i]['sources'].replace('[','').replace(']','').replace('not ','not_').replace(' ','')
            plan[i]['plan'] = plan[i]['plan'].replace('[','').replace(']','').replace('not ','not_').replace(' ','')
            
        new_list = []
        for dictionary in plan:
            if dictionary not in new_list:
                new_list.append(dictionary)
        plan = new_list.copy()

        # Find the outputs and the ground facts 
        outputs = list()
        ground_facts = list()
        for i in range(len(plan)):
            if plan[i]['type'] == 'OutputPlan':
                outputs.append(plan[i]['sources'])
            if plan[i]['type'] == 'FactInputPlan' or plan[i]['type'] == 'InputPlan':
                ground_facts.append(plan[i]['plan'])
            if plan[i]['type'] == 'JoinPlan':
                possible_facts = plan[i]['sources'].split('.,')
                if len(possible_facts) > 1:
                    new_source = list()
                    for j in possible_facts:
                        if '(' in j and j[-1] == '.':
                            new_source.append(j)
                        if '(' in j and j[-1] != '.':
                            new_source.append(j+'.')
                    plan[i]['sources'] = ','.join(new_source)

        
        # Discard from sources all ground facts
        for j in ground_facts:
            for i in range(len(plan)):
                if j+'(' not in plan[i]['sources'] and j in plan[i]['sources']:
                    plan[i]['sources'] = plan[i]['sources'].replace(j+',', '')
                    plan[i]['sources'] = plan[i]['sources'].replace(j, '')
                    
        # templates is a list of lists that will store all templates
        templates = list()
        for k in range(len(outputs)):
            if '.,' in outputs[k]:
                new_outputs = outputs[k].split('.,')
                for i in range(len(new_outputs)):
                    if new_outputs[i][-1] != '.':
                        new_outputs[i] = new_outputs[i] + '.'
                    templates.append([new_outputs[i]])
            else:
                templates.append([outputs[k]])

        # Starting from the outputs we go down iteratively the plan and generate the entire path.
        # In case a path gets splitted, a new template will be appended to the templates list
        # and will be later explored

        template_active = True # boolean to indicate that there are still templates to be generated
        N_template = 0 # number of templates
        aggregation_templates = []
        
        while template_active:
            # print(templates[N_template])
            path_active = True # boolean to indicate a path of the plan is not at the end yet
            if N_template == 0:
                I = 0
            else: 
                I = len(templates[N_template])-1

            while path_active:
                # print(templates[N_template])
                for j in range(len(plan)):
                    if I+1 <= len(templates[N_template]):
                        if templates[N_template][I] == plan[j]['plan']:
                            if plan[j]['sources'] != ',':
                                templates[N_template].append(plan[j]['sources'])

                templates[N_template] = list(dict.fromkeys(templates[N_template]))

                if I == len(templates[N_template]):
                    path_active = False

                # in case of OR conditions (two sources for the same atom) 
                # we split and add a new copied template
                if '.,' in templates[N_template][-1]:
                    split_step = templates[N_template][-1].split('.,')
                    # apply a function to generate the different possible paths
                    split_step = self.__split_branches_plan_step(split_step)
                    # split_step = split_branches_plan_step(split_step)

                    # Add templates
                    n = len(split_step)
                    index_of_templates = list()
                    index_of_templates.append(N_template)
                    for k in range(n-1):
                        templates.append(templates[N_template].copy())
                        index_of_templates.append(len(templates)-1)
                    if len(templates[N_template])>1:
                        if 'msum' in templates[N_template][-2]:
                            aggregation_templates.append(index_of_templates)
                    i = 0
                    for k in index_of_templates:
                        if len(split_step[i]) > 1:
                            templates[k][-1] = split_step[i][0]
                            for l in range(1, len(split_step[i])):
                                templates[k].append(split_step[i][1])
                        else:
                            templates[k][-1] = ','.join(split_step[i])
                        i += 1  
                        # if length of the path has not increased, it means that the path is at the end
                    
                I += 1
                if I == 25:
                    print('break issue!')
                    break

            # if no new template has been added we can stop the iterations
            if len(templates)-1 == N_template:
                    template_active = False
            else:
                N_template +=1
            

        for i in range(len(templates)):
            templates[i] = [ele for ele in templates[i] if ele != '']
            templates[i] = [ele.replace('not_','not ').replace('.,','.') for ele in templates[i]]
            templates[i] = list(dict.fromkeys(templates[i]))

        # print(templates)
        # print(aggregation_templates)

        if len(aggregation_templates) > 0:
        # Create aggregation templates
            for i in range(len(aggregation_templates)):
                aggr_template = []
                if len(aggregation_templates[i]) > 1:
                  if len(templates[aggregation_templates[i][0]]) == len(templates[aggregation_templates[i][1]]):
                    for k in range(len(templates[aggregation_templates[i][0]])):
                        if templates[aggregation_templates[i][0]][k] == templates[aggregation_templates[i][1]][k]:
                            aggr_template.append(templates[aggregation_templates[i][0]][k] )
                        else:
                            aggr_template.append(templates[aggregation_templates[i][0]][k] )
                            aggr_template.append(templates[aggregation_templates[i][1]][k] )
                    templates.append(aggr_template)
        

        return(templates)
    
    # To get a path verbalization we need to replace each vatom in each template
    # in this way we can then run the ProgramVerbalizer

    def __get_vatom(self, plan):
        temp_atoms = list()
        temp_body = list()
        for j in plan:
            if 'vatom' in j.split(':-')[0]:
                temp_atoms.append(j.split(':-')[0])
                temp_body.append(j.split(':-')[1])
        for i in range(len(temp_body)):
            temp_body[i] = temp_body[i][:-1]
        return temp_atoms, temp_body


    def __get_new_template(self, template):
        temp_heads, temp_bodies = self.__get_vatom(template)
        new_template = list()
        for j in range(len(template)):
            if 'vatom' not in template[j].split(':-')[0]:
                new_template.append(template[j])

        for j in range(len(new_template)):
            for i in range(len(temp_heads)):
                if temp_heads[i] in new_template[j]:
                    new_template[j] = new_template[j].replace(temp_heads[i],temp_bodies[i])
        
        return new_template

    def get_path_verbalizations(self, templates_cleaned, path_output, path_predicates, is_recursive = False):

        verb_temp = list()
        
        for temp in range(len(templates_cleaned)):
            with open(path_output + "verb_path_plan.json", "w") as out:
                out.write('[')
                first_step = True
                for step in templates_cleaned[temp]:
                    if first_step:
                        first_step = False
                    else:
                        out.write('\n,')
                    vstep = {"rule": step} 
                    json.dump(vstep, out, separators=(",", ":"))
                out.write(']')
            
            path_verb_chase = os.path.join(path_output, 'verb_path_plan.json')
            
            program_verb = ProgramVerbalizer.ProgramVerbalizer()
            program_verb.verbalize_program(path_verb_chase, path_predicates, path_output, is_recursive)
            
            path_verb_chase = os.path.join(path_output, 'verb_program.txt')

            with open(path_verb_chase) as f:
                lines = f.readlines()

            for i in range(len(lines)):
                lines[i] = lines[i].replace('\n','')

            verb_temp.append(lines)

        return verb_temp
    
    def __get_indirect_recursive_templates(self, templates, templates_unfolded):

        # # Create indirect recursion templates
        for i in range(len(templates)):
            heads = []
            for j in range(len(templates_unfolded[i])):
                heads.append(templates_unfolded[i][j].split('(')[0])

            if all(heads.count(x) < 2 for x in heads):
                continue

            is_ind, rec_rule, init_rule = self.identify_indirect_recursion(templates_unfolded[i], plan_search = True)
            # print(is_ind)
            if is_ind:
                templates.append(templates[i].copy())
                templates_unfolded.append(templates_unfolded[i].copy())
                templates[-1] = [item for item in templates[-1] if init_rule not in item]
                templates_unfolded[-1] = [item for item in templates_unfolded[-1] if init_rule not in item]

    def get_program_paths(self, plan_path, generic_path_output, path_predicates):
        templates = self.__get_templates(plan_path)
        templates = [list(tupl) for tupl in {tuple(item) for item in templates }]
        templates_to_verb = list()
        for i in range(len(templates)):
            templates_to_verb.append(self.__get_new_template(templates[i]))
       
        self.__get_indirect_recursive_templates(templates, templates_to_verb)

        templates_verb = self.get_path_verbalizations(templates_to_verb, generic_path_output, path_predicates)
        
        if os.path.exists(os.path.join(generic_path_output, 'verb_path_plan.json')):
            os.remove(os.path.join(generic_path_output, 'verb_path_plan.json'))
    
        if os.path.exists(os.path.join(generic_path_output, 'verb_program.txt')):
            os.remove(os.path.join(generic_path_output, 'verb_program.txt'))
        
        for i in range(len(templates)):
            templates[i].reverse()
            templates_to_verb[i].reverse()
            templates_verb[i].reverse()

        return templates, templates_to_verb, templates_verb
    
    def get_recursive_template(self, templates,path_output,path_predicates):

        recursive_templates = []
        verb = []

        for plan in templates[1]:
            for rule in plan:
                # print(rule)
                head, body = rule.split(":-")[0], rule.split(":-")[1]
                body = '-'+body
                if ','+head.split("(")[0] in body or '-'+head.split("(")[0] in body:
                    recursive_templates.append(plan.copy())
                    verb.append(self.get_path_verbalizations(recursive_templates, path_output, path_predicates, True)[0])
                    break
        
        return(recursive_templates,verb)


    def unfolding(self, fact_rules, recursive_case):
        unfolded_chase = []
        to_unfold = []

        # Detect recursive rules in a chase of an instance
        for rule in fact_rules:
            # print(rule)
            if rule['atom'].split('(')[0] not in rule['body']:
                unfolded_chase.append(rule.copy())
            else:
                to_unfold.append(rule.copy())


        # If there are recursive rules to unfold
        if len(to_unfold) > 0 and recursive_case:
            check_unfold = True
            # Until completely unfolded
            while check_unfold:
                # starting from last recursive application
                initial = to_unfold[-1]['body']
                # For each recursion
                for fact in to_unfold:
                    # print(fact)
                    if fact['atom'] in to_unfold[-1]['body']:
                        # print(to_unfold[-1]['atom'])
                        if fact['body'].split('),')[-1].split('(')[0] not in to_unfold[-1]['atom']:
                            to_unfold[-1]['body'] = to_unfold[-1]['body'].replace(fact['atom'],'),'.join(fact['body'].split('),')[:-1])+')')
                        if fact['body'].split('),')[-1].split('(')[0] in to_unfold[-1]['atom']:
                            to_unfold[-1]['body'] = to_unfold[-1]['body'].replace(fact['atom'],'),'.join(fact['body'].split('),'))+')')
                if to_unfold[-1]['body'] == initial:
                        check_unfold = False

            return unfolded_chase + [to_unfold[-1]]
        elif len(to_unfold) > 0 and not recursive_case:
            return fact_rules
        else: 
            return fact_rules
    
    def empty_rule(self, rule):
        ############# To do
        rule = rule.replace('not ','')
        ###################
        if '),' in rule and 'msum' not in rule:
            no_var_rule = re.sub("\(.*?\)","()",rule).split('),')
        else:
            if 'msum' in rule:
                no_var_rule = re.sub("\(.*?\)","()",rule).split(',')[:-1]
                no_var_rule = ','.join(no_var_rule)
            else:
                no_var_rule = [re.sub("\(.*?\)","()",rule).replace('.','')]
        if ':-' not in no_var_rule[-1] and len(no_var_rule)>1:
            conditions = no_var_rule[-1].split(',')
            for p in range(len(conditions)):
                if '<>' in conditions[p]:
                    conditions[p] = '<>'
                else:
                    if '>' in conditions[p]:
                        conditions[p] = '>'
                    if '<' in conditions[p]:
                        conditions[p] = '<'
                if '=' in conditions[p]:
                    conditions[p] = '='
            conditions = ','.join(conditions)
            no_var_rule = '),'.join(no_var_rule[:-1])+'),'+conditions
        else:
            if len(no_var_rule)>1:
                no_var_rule = '),'.join(no_var_rule[:-1])
            else:
                no_var_rule = no_var_rule[0]
        
        return no_var_rule
    
    def identify_indirect_recursion(self, chase, plan_search = False):
        
        idb_predicates = []

        # Get all IDB predicates
        for rule in chase:
            idb_predicates.append(rule.split('(')[0])
        
        # Drop one-only predicates 
        idb_predicates_clean = [i for i in idb_predicates if idb_predicates.count(i)>1]

        # Get bodies
        body_rules =[]
        head_rules = []
        for rule in chase:
            head_rules.append(rule.split(':-')[0])
            body_rules.append(rule.split(':-')[1])
        
        recursive_pred = []
        for i in range(len(idb_predicates_clean)):
            reference_rule = []
            for h in range(len(head_rules)):
                if idb_predicates_clean[i] in head_rules[h]:
                    reference_rule.append(body_rules[h])
            for rule in reference_rule:
                if any(idb in rule for idb in idb_predicates_clean) == False:
                    recursive_pred.append(idb_predicates_clean[i])    
        recursive_pred = list(dict.fromkeys(recursive_pred))

        recursive_rule = []
        for atom in recursive_pred:
            for i in range(len(body_rules)):
                predicate_rule = body_rules[i].split('(')
                if ')' not in predicate_rule[-1]:
                    predicate_rule = predicate_rule[:-1]
                # if atom in head_rules[i] and any(idb in body_rules[i] for idb in idb_predicates_clean) == True:
                if atom in head_rules[i] and any(idb in body_rules[i] for idb in idb_predicates) == True and atom not in predicate_rule:
                    recursive_rule.append(body_rules[i])
                if atom in head_rules[i] and body_rules[i] not in recursive_rule:
                    initializer_rule = body_rules[i]
        recursive_rule = list(dict.fromkeys(recursive_rule))
        # print(recursive_rule)

        if plan_search and len(recursive_rule) > 0:
            return True, recursive_rule, initializer_rule
        elif plan_search and len(recursive_rule) == 0:
            return False, [], []

        if len(recursive_rule) > 1:
            return True, recursive_rule, initializer_rule
        else:
            return False, [], []
        

    def reorder_verbalization(self, verb_json, atom_chase, chase_fact):

        new_verb = []
        for atom in atom_chase:
            # print(atom)
            for verb in verb_json:
                if atom == verb['atom']:
                    new_verb.append(verb)
                    # print(verb['atom'])

        new_verb.reverse()
        msum_order_verb = []
        seen = []
        for verb in new_verb:
            # print(verb)
            if verb['atom'] not in seen:
                if 'msum' not in verb['body']:
                    msum_order_verb.append(verb)
                else:
                    # check consistency
                    if verb['atom'].split('(') != new_verb[0]['atom'].split('('):
                        msum_order_verb.append(verb)
                    else:
                        msum_order_verb.append(verb)
                        for verb2 in new_verb:
                            if verb2['atom'] in verb['body']:
                                msum_order_verb.append(verb2)
                                seen.append(verb2['atom'])
                                
        msum_order_verb.reverse()
        
        chase_fact.reverse()

        for k in range(len(chase_fact)):
            # If vatom in body
            if 'vatom' in chase_fact[k].split(':-')[1]:
                #search for that vatom
                # print(chase_fact[k])
                for fact2 in chase_fact:
                    if fact2.split(':-')[0] in chase_fact[k].split(':-')[1] and 'vatom' in fact2.split(':-')[0]:
                        chase_fact[k] = chase_fact[k].replace(fact2.split(':-')[0], fact2.split(':-')[1][:-1])
                        break

        msum_order_chase = []
        for atom in msum_order_verb:
            for i in range(len(atom_chase)):
                if atom['atom'] == atom_chase[i]:
                    msum_order_chase.append(chase_fact[i])
        msum_order_chase.reverse()

        return msum_order_verb, msum_order_chase


    def mapping_to_template(self, chase, atom_chase, templates, templates_rec, path_output, fact_to_explain, path_verb_chase):
        # print('\n')
        # print(fact_to_explain)
        # print('Mapping:')
 
        # First, retrieve from the chase all facts
        explain_derivation = True
        AggregateVerbalizer.VerbalizationFinder().verbalize_fact(path_verb_chase, path_output, fact_to_explain, explain_derivation)

        with open(os.path.join(path_output, 'verb_fact.json')) as c:
            original = json.load(c)
        realization = original.copy()
        chase_fact = chase.copy()
        
        # Drop useless facts (derived from msum and not used)
        atom_to_remove = []
        index = []
        for i in range(len(realization)):
            potential_atom_to_drop = realization[i]['atom']
            useful_atom = False
            for j in range(len(realization)):
                if potential_atom_to_drop in realization[j]['body']:
                        useful_atom = True
            if useful_atom == True and potential_atom_to_drop not in atom_chase and len(realization[i]['body'])>0:
                    atom_to_remove.append(potential_atom_to_drop)
                    index.append(i)
            if useful_atom == False and potential_atom_to_drop != fact_to_explain:
                atom_to_remove.append(potential_atom_to_drop)
                index.append(i)
        for i in sorted(index, reverse=True):
            del realization[i]
        for i in atom_to_remove:
            for j in range(len(atom_chase)):
                if i == atom_chase[j]:
                    del chase_fact[j]

        # Reorder realization json according to reasoning
        recursive_case = False
        for p in range(1,len(chase_fact)-1):
            if chase_fact[p] == chase_fact[p-1] and 'vatom' not in chase_fact[p].split(':-')[0]:
                recursive_case = True
        atom2 = atom_chase.copy()
        atom2.reverse()
        # for ll in realization:
        #     print(ll['atom'])

        realization, chase_fact = self.reorder_verbalization(realization, atom2, chase_fact)
        
        # Unfold if direct recursion
        realized_rule = []
        unfolded_chase = self.unfolding(realization, recursive_case)

        for j in unfolded_chase:
            if j['body']:
                realized_rule.append(j['atom']+':-'+j['body'])
        # print(realized_rule)
        # Indirect recursion
        indirect_recursion, rec_body, initializer = self.identify_indirect_recursion(realized_rule)
        if indirect_recursion == False:
            chase_splits = [list(dict.fromkeys(chase_fact))]
            realized_rule = [realized_rule]
        else:
            chase_splits = []
            real_rule = []
            chase_fact.reverse()
            i = 0
            l = 0
            for g in range(len(rec_body)):
                k = 0
                for j in range(len(realized_rule)):
                    if 'vatom' in chase_fact[k]:
                        k += 1
                    if rec_body[g] in realized_rule[j]:
                        chase_splits.append(chase_fact[i:k+1])
                        real_rule.append(realized_rule[l:j+1])
                        i = k+1
                        l = j+1
                    k += 1
            realized_rule = real_rule
        # print(realized_rule)
        if recursive_case == False and indirect_recursion == False:
            chase_splits = [list(dict.fromkeys(chase_fact))]

        final_verb = []

        # print(templates)

        for r in range(len(chase_splits)):
            found = False
            for i in range(len(templates[0])):
                # print(templates[1][i])
                if sorted(templates[1][i])==sorted(list(dict.fromkeys(chase_splits[r]))) and recursive_case == False:
                    found = True
                    chase_cleaned = templates[1][i]
                    extracted_template = templates[3][i]
                    break

            if found == False:
                for i in range(len(templates_rec[0])):
                    chase_splits[r] = list(dict.fromkeys(chase_splits[r]))
                    if sorted(templates_rec[0][i])==sorted(chase_splits[r]):
                        chase_cleaned = templates_rec[0][i]
                        extracted_template = templates_rec[-1][i]

            # Map to abstract form of rule
            rules = []
            for map_to_rule in realized_rule[r]:
                empty_realized_rule = self.empty_rule(map_to_rule)
                for potential_rule in chase_cleaned:
                    potential_rule_empty = self.empty_rule(potential_rule)
                    if potential_rule_empty[:-1] in empty_realized_rule:
                        rules.append(potential_rule[:-1])

            # print(rules)
            # print(realized_rule[r])

            # Create the dictionary to map variables to constants
            dict_map = {}
            for i in range(len(rules)):

                is_aggregation = False
                rules[i] = split_condition_from_rule(rules[i])[0][:-1]
                if 'msum' in realized_rule[r][i]:
                    is_aggregation = True
                realized_rule[r][i] = split_condition_from_rule(realized_rule[r][i])[0][:-1]
                
                # print(rules[i])
                # print(realized_rule[r][i])
                head, body = rules[i].split(':-')[0],rules[i].split(':-')[1]
                head_r, body_r = realized_rule[r][i].split(':-')[0],realized_rule[r][i].split(':-')[1]

                # Get constants of the head inside the dictionary
                # print('Map Head')
                vars = head.split('(')[1].split(')')[0].split(',')
                vars_r = head_r.split('(')[1].split(')')[0].split(',')
                # print(vars)
                # print(vars_r)
                for j in range(len(vars)):
                    # if is_aggregation:
                        if vars[j] not in dict_map.keys():
                            dict_map.update({vars[j]:vars_r[j]})
                        else:
                            if vars_r[j] not in dict_map[vars[j]]:
                                dict_map.update({vars[j]:dict_map[vars[j]]+' and ' +vars_r[j]})
                    # else:
                        # dict_map.update({vars[j]:vars_r[j]})
                # print(dict_map)
                
                # print("Map body")
                # Analyse the body: check if it is recursive
                if head.split("(")[0] not in body:
                    #in case no recursion we add variables of the body inside the dictionary
                    body = body.split('),')
                    body_r = body_r.split('),')
                    
                    for j in range(len(body_r)):
                        predicate = body_r[j].split('(')[0]
                        for s in body:
                            if predicate in s:
                                body_abstract = s
                        vars = body_abstract.split('(')[1].split(')')[0].split(',')
                        vars_r = body_r[j].split('(')[1].split(')')[0].split(',')
                        # print(vars)
                        # print(vars_r)
                        for k in range(len(vars)):
                            if vars[k] not in dict_map.keys():
                                dict_map.update({vars[k]:vars_r[k]})
                            else:
                                if vars_r[k] not in dict_map[vars[k]]:# and is_aggregation:
                                    dict_map.update({vars[k]:dict_map[vars[k]]+' and ' + vars_r[k]})
                                    
                elif head.split("(")[0] in body and recursive_case:
                    body = body.split('),')
                    body_r = body_r.split('),')
                    body_nor = [body_r[0],body_r[-1]]
                    for j in range(len(body)):
                        vars = body[j].split('(')[1].split(')')[0].split(',')
                        vars_r = body_nor[j].split('(')[1].split(')')[0].split(',')
                        index = list()
                        for k in range(len(vars)):
                            if vars[k] not in dict_map.keys():
                                dict_map.update({vars[k]:vars_r[k]})
                            else:
                                index.append(k)
                    
                    intermediates = [body_r[1:-1]]

                    for j in range(len(intermediates)):
                        is_already_dict = False
                        for k in intermediates[j]:
                            ll = k.split('(')[1].split(',')
                            for p in index:
                                if ll[p] not in dict_map.values() and is_already_dict:
                                    if 'and '+ll[p] not in dict_map['ENTITY']:
                                        dict_map.update({'ENTITY':dict_map['ENTITY'] + ' and ' +ll[p]})
                                if ll[p] not in dict_map.values() and is_already_dict == False:
                                    dict_map.update({'ENTITY':ll[p]})
                                    is_already_dict = True
                    # print(dict_map)
                
                else:
                    #in case no recursion we add variables of the body inside the dictionary
                    body = body.split('),')
                    body_r = body_r.split('),')

                    for j in range(len(body_r)):
                        predicate = body_r[j].split('(')[0]
                        for s in body:
                            if predicate in s:
                                body_abstract = s
                        vars = body_abstract.split('(')[1].split(')')[0].split(',')
                        vars_r = body_r[j].split('(')[1].split(')')[0].split(',')
                        # print(vars)
                        # print(vars_r)
                        for k in range(len(vars)):
                                if vars[k] not in dict_map.keys():
                                    dict_map.update({vars[k]:vars_r[k]})
                                else:
                                    if vars_r[k] not in dict_map[vars[k]]:
                                        dict_map.update({vars[k]:dict_map[vars[k]]+' and ' + vars_r[k]})
                        # print(dict_map) 
            # print(dict_map)
            extracted_template = extracted_template.replace(',',' ,').replace('\'',' \'').replace('.',' .')\
                            .replace('%',' %').replace('*',' * ').replace('+',' + ').replace('-',' - ').replace('/',' / ')\
                            .replace('(','( ').replace(')',' )')
            extracted_template = extracted_template.split()

            for i in range(len(extracted_template)):
                if extracted_template[i] in dict_map.keys():
                    extracted_template[i] = dict_map[extracted_template[i]]

            para_v = ' '.join(extracted_template).replace(' ,',',').replace(' \'','\'').replace(' .','.')\
                            .replace(' %','%').replace(' * ',' x ').replace(' + ','+').replace(' - ','-').replace(' / ','/').replace('--','+')\
                            .replace('( ','(').replace(' )',')').replace('and ENTITY','').replace('_', ' ')

            final_verb.append(para_v)

        record_verb = list()
        for i in range(len(realization)):
            record_verb.append(realization[i]['Verb_rule'])

        df = pd.DataFrame([[fact_to_explain,' '.join(record_verb), ' '.join(final_verb)]], columns = ['Derived Fact','DeterministicVerbalization', 'TemplateApproach'])

        if os.path.exists(os.path.join(path_output, 'verb_fact.json')):
            os.remove(os.path.join(path_output,'verb_fact.json'))
        
        return df