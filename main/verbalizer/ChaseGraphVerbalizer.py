import json
import logging
from utilsFunctions import split_condition_from_rule

'''
    This class performs the verbalization of the chase graph.
    
    It receives as input a num_chase_graph.json file with the chase steps performed in an execution,
    in the form:
    [{"name":generated fact,"pattern":whether the args are constants or nulls,
    "provenance":list of the parent facts,"rule":the activated rule for this chase step,
    "number":list of the parents as hierarchical numbers}
    ]
    and a predicates.json file with the verbalized descriptions of the predicates involved
    in the chase, in the form:
    [{"predicate":predicate with generic args,"description":generic verbalization of the predicate}
    ]
    
    It returns a verb_chase_graph.json file with the verbalization of each chase step, in the form:
    [{"sentence":the verbalized chase step,"number":list of the parents as hierarchical numbers}
    ]
    
    __author__: teodorobaldazzi
    __author__: andreacolombo
'''
class ChaseGraphVerbalizer:

    logging.getLogger().setLevel(logging.INFO)


    '''
        :param preds_descr: the deserialized pred_file
        :param fact: a fact in the chase of that predicate
        :param fact_pattern: the pattern of the args in the fact
        :param nulls_in_step: a list of nulls already verbalized for the current chase step    
    '''
    def __get_fact_description(self, preds_descr, fact, fact_pattern, nulls_in_step):
        # extract name, args and pattern of the current fact
        fact_name = fact.partition('(')[0]
        fact_args = fact.split('(')[1].split(')')[0].split(',')
        fact_pattern_args = fact_pattern.split('(')[1].split(')')[0].split(',')

        # for each predicate in the file (until the right description is found)
        for pred_descr in preds_descr:
            # extract name and args of the predicate
            pred = pred_descr['predicate']
            pred_name = pred.partition('(')[0]
            pred_parts = pred.split('(')[1].split(')')[0].split(',')
            # if the fact belongs to the current predicate
            if pred_name == fact_name and len(pred_parts) == len(fact_args):
                # extract the description of the predicate
                fact_descr = pred_descr['description']
                # extract the specifics of the predicate terms
                pred_terms_specifics = pred_descr['specifics']['terms']

                # verbalize the fact according to the description of the predicate
                # by substituting the generic args of the predicate with the real ones of the fact
                for i in range(len(pred_parts)):
                    fact_arg = fact_args[i]
                    # if this arg is a null and it has not already been encountered in the current chase step
                    if int(fact_pattern_args[i]) < 0 and fact_arg not in nulls_in_step:
                        # verbalize the new null
                        fact_descr = fact_descr.replace(pred_parts[i],
                                                        "there exists some unknown entity labelled as " + fact_arg + " that")
                        # update the list
                        nulls_in_step.append(fact_arg)
                    # if this arg is a constant or an already encountered null in the current chase step
                    else:
                        # verbalize the constant or the already encountered null
                        # distinguish between constants corresponding to an entity or to a value
                        constant_type = pred_terms_specifics[i]['type']
                        if constant_type == 'entity':
                            fact_arg = "\"" + fact_arg + "\""
                        fact_descr = fact_descr.replace(pred_parts[i], ' ' + fact_arg)
                # the chase step has been verbalized, so return it
                return fact_descr
        return None


    '''
        :param chase: the deserialized chase_file 
        :param fact: a fact in the chase
    '''
    # def __get_fact_pattern(self, chase, fact):
    #     for step in chase:
    #         if step['name'] == fact:
    #             return step['pattern']
    #     return None
    def __get_fact_pattern(self, chase, fact):
        for step in chase:
            if step['name'].split('(')[0] == str(fact).split('(')[0]:
                return step['pattern']
        return None


    '''
        :param chase: the deserialized chase_file 
        :param fact: a fact in the chase
    '''
    def __get_fact_provenance(self, chase, fact):
        for step in chase:
            if step['name'] == fact:
                return step['provenance']
        return None


    '''
        :param step: a step of the chase
    '''
    # TODO: add the case of negated with existential such as: not own(X,_,_)
    def __get_negated_fact(self, step):
        # given that only one negation per rule is activated there will be only
        # one negated atom in a single step -> it is all that we need
        negated_pred = step['rule'].split('not ')[1].split(')')[0] + ')'
        # each variable of the negated atom must have a ward in another predicate of the same rule
        need_ward = negated_pred.split('(')[1].split(')')[0].split(',')
        predicate_rule = step['rule'].split(':-')[1].split('),')

        # as the provenance is null when there is a derived fact which depend on a negation
        # we have to "build" the negated fact by ourselves, exploting the feature of wardness
        for k in range(len(need_ward)):
            # for each variable of the negated atom we must find the ward
            for i in range(len(predicate_rule)):
                # check which atom is warding, excluding negated ones
                if predicate_rule[i][:3] != 'not ':
                    # for each predicate look at its contents
                    var_pred = str(str(predicate_rule[i]).split('(')[1]).replace(')','').split(',')
                    # loop to check which one is used in negation
                    for j in range(len(var_pred)):
                        if need_ward[k] == var_pred[j]:
                            null_descr = str(str(str(step['provenance'].split('[')[1].split(']')[0].split(', ')[i]).split('(')[1]).split(')')[0]).split(',')[j]
                            need_ward[k] = null_descr


        negated_fact = str(negated_pred.split('(')[0]+'('+','.join(need_ward)+')')

        return negated_fact


    '''
        :param condition: a condition of a rule
        :param step: a step of the chase
    '''
    def __get_conditioned_fact(self, condition, step):
        # identify the variable subject to condition
        condition = condition.split('>=')[0]
        condition = condition.split('<=')[0]
        condition = condition.split('<>')[0]
        condition = condition.split('!=')[0]
        condition = condition.split('>')[0]
        condition = condition.split('<')[0]
        condition = condition.split('=')[0]
        # extract from body the predicates and split them
        predicate_rule = step['rule'].split(':-')[1].split('.')[0].split('),')
        # identify through the provenance the corresponing realization subject to condition
        for i in range(len(predicate_rule)):
            if predicate_rule[i][:3] != 'not ':
                var_pred = str(str(predicate_rule[i]).split('(')[1].replace(')','')).split(',')
                for j in range(len(var_pred)):
                    if condition == var_pred[j]:
                        null_descr = str(str(str(step['provenance'].split('[')[1].split(']')[0].split(', ')[i]).split('(')[1]).split(')')[0]).split(',')[j]
                        condition = null_descr

        return condition

    '''
        :param condition: a condition of a rule
        :param step: a step of the chase
    '''
    # same thing but on the other side of the condition operator
    # different things depending on whether the 'conditioning' is a number/string or another variable
    def __get_conditioning_fact(self, condition, step):
        try:
            # identify the variable subject to condition
            if '>=' in condition:
                condition = condition.split('>=')[1]
            if '<=' in condition:
                condition = condition.split('<=')[1]
            if '<>' in condition:
                condition = condition.split('<>')[1]
            if '!=' in condition:
                condition = condition.split('!=')[1]
            if '>' in condition:
                condition = condition.split('>')[1]
            if '<' in condition:
                condition = condition.split('<')[1]
            if '=' in condition:
                condition = condition.split('=')[1]
            # extract from body the predicates and split them
            predicate_rule = step['rule'].split(':-')[1].split('.')[0].split('),')
            # identify through the provenance the corresponing realization subject to condition
            for i in range(len(predicate_rule)):
                if predicate_rule[i][:3] != 'not ':
                    var_pred = str(str(predicate_rule[i]).split('(')[1].replace(')','')).split(',')
                    for j in range(len(var_pred)):
                        if condition == var_pred[j]:
                            null_descr = str(str(str(step['provenance'].split('[')[1].split(']')[0].split(', ')[i]).split('(')[1]).split(')')[0]).split(',')[j]
                            condition = null_descr

        except:
            if '>=' in condition:
                condition = condition.split('>=')[1]
                return(condition)
            if '<=' in condition:
                condition = condition.split('<=')[1]
                return(condition)
            if '<>' in condition:
                condition = condition.split('<>')[1]
                return(condition)
            if '!=' in condition:
                condition = condition.split('!=')[1]
                return(condition)
            if '>' in condition:
                condition = condition.split('>')[1]
                return(condition)
            if '<' in condition:
                condition = condition.split('<')[1]
                return(condition)
            if '=' in condition:
                condition = condition.split('=')[1]
                return(condition)

        return condition
    
    '''
        :param step: a step of the chase
        :param oper: an algebric operation of a rule
    '''
    def __get_realized_head(self, step, oper):
        formula = oper.split('=')[1]
        oper = oper.split('=')[0]
        head_rule = step['rule'].split(':-')[0].split(')')[0].split('(')[1].split(',')
        name_head = step['name'].split(')')[0].split('(')[1].split(',')
        formula_sep = formula.replace('+', ' + ').replace('-',' - ').replace('*',' * ').replace('/',' / ').replace('(',' ( ').replace(')',' ) ').replace('msum','msum ').split(' ')
        variables = step['rule'].split(':-')[1].split(')')[0].split('(')[1].split(',')
        constants = step['original_provenance'].replace('[','').replace(']','').split('(')[1].split(')')[0].split(',')

        for j in range(len(formula_sep)):
            for i in range(len(variables)):
                if formula_sep[j] == variables[i]:
                     formula_sep[j] = constants[i]
                     break

        for i in range(len(head_rule)):
            if head_rule[i] == oper:
                if 'msum' not in formula:
                    result_operation = name_head[i]
                    return ', with ' + result_operation + ' given by ' + ''.join(formula_sep)
                else:
                    result_operation = name_head[i]
                    verb_msum = ', with ' + result_operation + ' given by the sum over all the contributors' # + \
                       # formula.split('msum')[1].split(',')[1].replace('(','').replace(')','')
                    verb_msum = verb_msum.replace('<','').replace('>','')
                    return verb_msum
        return ''
    
    '''
        This method creates a .json file with the verbalized chase graph
        
        :param chase_path: path to the num_chase_graph.json file with the chase graph numbered
        :param predicates_path: path to the predicates.json file with the predicates' description
        :param output_path: path to output file        
    '''
    def verbalize_chase_graph(self, num_chase_path, predicates_path, output_path):
        try:
            with open(num_chase_path) as c:
                # deserialize chase file
                chase = json.load(c)
                with open(predicates_path) as p:
                    # deserialize pred file
                    preds_descr = json.load(p)
                    # get a list of predicates name: useful for identifying temp atoms
                    preds_name = list()
                    for k in preds_descr:
                        preds_name.append(k['predicate'].split('(')[0] +'(')

                    # create new output file or rewrite existing one
                    with open(output_path + "verb_chase_graph.json", "w") as out:
                        out.write('[')
                        first_step = True
                        # for each line in the chase file, i.e., for each step of the chase,
                        # we split the body between predicates and eventual conditions on variables
                        # -> useful for verbalizing conditions
                        for step in chase:
                            # if step['rule']:
                            #     # replace "not " occurrences with "not_"
                            #     step['rule'] = step['rule'].replace("not ", "not_")
                            #     # remove all whitespaces
                            #     step['rule'] = step['rule'].replace(" ", "")
                            # # split conditions from the rule
                            step['rule'], step['conditions'], step['algebric'] = split_condition_from_rule(step)
                            step['original_provenance'] = step['provenance']

                        # for each chase step
                        for step in chase:
                            if step['number'] != -1:
                                realized_atom = list()
                                nulls_in_step = []  # list to keep track of nulls in that step
                                # extract from provenance the facts activating the body of the rule
                                body = step['provenance'].split('[')[1].split(']')[0].split(', ')

                                # Retrieve contributors to msum
                                if step['algebric'] and len(body)>1:
                                    if 'msum' in step['algebric'][0]:
                                        multiple = list()
                                        for join_fact_temp in body:
                                                if 'vatom' in join_fact_temp:
                                                    multiple += self.__get_fact_provenance(chase, join_fact_temp).split(
                                                    '[')[1].split(']')[0].split(', ')
                                                else:
                                                    multiple += [join_fact_temp]
                                        while 'vatom' in ','.join(multiple):
                                            index_to_del = []
                                            for deep in range(len(multiple)):
                                                if 'vatom' in multiple[deep]:
                                                    multiple += self.__get_fact_provenance(chase, multiple[deep]).split('[')[1].split(']')[0].split(', ')
                                                    index_to_del.append(deep)
                                            for ind in sorted(index_to_del, reverse=True):
                                                del multiple[ind]

                                        body = multiple
                                        replace_temp = "["
                                        is_temp = True

                                # if it is a chase step, i.e., it involves the derivation of an intensional fact
                                if body[0] and body[0] != 'null':
                                    # verbalize the body
                                    body_descr = ""
                                    # this is the case of linear rules
                                    if len(body) == 1:
                                        is_temp = False
                                        # extract the pattern of the body fact:
                                        # if it is not a temporal atom (vatom) it can be verbalized, otherwise
                                        # it must be further expanded with its provenance
                                        if body[0][:5] != 'vatom':
                                            body_pattern = self.__get_fact_pattern(chase, body[0])
                                            # verbalize the linear body
                                            body_descr = "Since " + self.__get_fact_description(preds_descr, body[0],
                                                                                                body_pattern, nulls_in_step)
                                            realized_atom.append(body[0])

                                        else:
                                            body = self.__get_fact_provenance(chase, body[0]).split('[')[1].split(']')[0].split(', ')
                                            # change boolean to indicate that temporal provenance atoms must be replaced iteratively
                                            is_temp = True
                                            # new provenance for temporal atom
                                            replace_temp = "["

                                    # this is the case of join rules
                                    if len(body) > 1:
                                        # for each temp fact involved in the join
                                        for join_fact_temp in body:
                                            # check if there is a negated atom
                                            if join_fact_temp != 'null' and join_fact_temp.split('(')[0]+('(') not in preds_name:
                                                # determine the real fact involved in the join by extracting
                                                # the provenance of the temp one
                                                # temp facts (used for joins) will always have a single fact as provenance
                                                join_fact_real = self.__get_fact_provenance(chase, join_fact_temp).split(
                                                    '[')[1].split(']')[0].split(', ')

                                                for multiple_real_facts in join_fact_real:
                                                    if is_temp:
                                                        if multiple_real_facts:
                                                            replace_temp += multiple_real_facts + ', '
                                                        else:
                                                            replace_temp += join_fact_temp + ', '

                                                    else:
                                                        # extract the pattern of the real body fact
                                                        body_pattern = self.__get_fact_pattern(chase, multiple_real_facts)
                                                        # verbalize the join body
                                                        # distinct verbalization if it is the first fact in the join
                                                        if body_descr == "":
                                                            body_descr = "Since " \
                                                                        + self.__get_fact_description(preds_descr, multiple_real_facts,
                                                                                                        body_pattern, nulls_in_step)
                                                            realized_atom.append(multiple_real_facts)

                                                        else:
                                                            body_descr += ", and " \
                                                                        + self.__get_fact_description(preds_descr, multiple_real_facts,
                                                                                                        body_pattern, nulls_in_step)
                                                            realized_atom.append(multiple_real_facts)

                                            # same things but for negated atoms
                                            elif join_fact_temp == 'null' and join_fact_temp.split('(')[0]+('(') not in preds_name:
                                                if body_descr == "":
                                                    negated_atom = self.__get_negated_fact(step)
                                                    body_descr += 'Since it is not true that ' + \
                                                                  self.__get_fact_description(preds_descr, negated_atom,
                                                                                                self.__get_fact_pattern(chase, negated_atom),
                                                                                                nulls_in_step)
                                                    realized_atom.append(negated_atom)
                                                else:
                                                    negated_atom = self.__get_negated_fact(step)
                                                    body_descr += ', and it is not true that ' + \
                                                                  self.__get_fact_description(preds_descr, negated_atom,
                                                                                              self.__get_fact_pattern(chase, negated_atom),
                                                                                              nulls_in_step)
                                                    realized_atom.append(negated_atom)
                                            else:
                                                # if there is an algebric rule just need to replace the provenance with
                                                # the facts that were retrieved before
                                                replace_temp += join_fact_temp + ', '

                                        if is_temp:
                                            # replace provenance
                                            replace_temp = replace_temp[:-2] + ']'
                                            step['provenance'] = replace_temp
                                            is_temp = False


                                    body = step['provenance'].split('[')[1].split(']')[0].split(', ')
                                    if len(body) == 1:
                                        # if body[0].startswith('vatom'):
                                        #    body = self.__get_fact_provenance(chase, body[0]).split('[')[1].split(']')[0].split(', ')
                                        body_pattern = self.__get_fact_pattern(chase, body[0])
                                        # verbalize the linear body
                                        body_descr = "Since " + self.__get_fact_description(preds_descr, body[0],
                                                                                            body_pattern, nulls_in_step)
                                        # realized_atom.append(body[0])


                                    # in case of an algebric in the step
                                    if len(body) > 1 and step['name'].split('(')[0]+'(' in preds_name and not body_descr:

                                        for predicates_operation in body:
                                            body_pattern = self.__get_fact_pattern(chase, predicates_operation)
                                            if body_descr == "":
                                                body_descr = "Since " \
                                                     + self.__get_fact_description(preds_descr, predicates_operation,
                                                                                    body_pattern, nulls_in_step)
                                                realized_atom.append(predicates_operation)
                                            else:
                                                body_descr += ", and " \
                                                    + self.__get_fact_description(preds_descr, predicates_operation,
                                                                                    body_pattern, nulls_in_step)
                                                realized_atom.append(predicates_operation)

                                    len_r = len(realized_atom)
                                    try:
                                        if propagate_condition:
                                            realized_atom.append(propagate_condition)
                                            del propagate_condition
                                    except: None

                                    algebric_descr = ""
                                    # verbalize algebric operation
                                    if len(step['algebric']) > 0:
                                        for oper in step['algebric']:
                                            if '=' in oper:
                                                algebric_descr += self.__get_realized_head(step, oper)
                                                realized_atom.append(oper)

                                    # add verbalizations of (eventual) conditions
                                    if len(step['conditions']) > 0:
                                        if len(realized_atom) > len_r and len(step['algebric']) == 0:
                                            realized_atom = realized_atom[:-1]
                                        # if there is a condition and no body descr yet, it means that
                                        # it was a temporal atom and a description can be created
                                        if len(body_descr) == 0:
                                            for predicates_operation in body:
                                                body_pattern = self.__get_fact_pattern(chase, predicates_operation)
                                                if body_descr == "":
                                                    body_descr = "Since " \
                                                        + self.__get_fact_description(preds_descr, predicates_operation,
                                                                                        body_pattern, nulls_in_step)
                                                    realized_atom.append(predicates_operation)
                                                else:
                                                    body_descr += ", and " \
                                                        + self.__get_fact_description(preds_descr, predicates_operation,
                                                                                        body_pattern, nulls_in_step)
                                                    realized_atom.append(predicates_operation)
                                        conditions = step['conditions']
                                        conditions_descr = ''
                                        for cond in conditions:
                                            # different verbalization according to condition
                                            if '>=' in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is equal to or over ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '>=' + self.__get_conditioning_fact(cond, step))
                                            if '<=' in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is equal to or under ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '<=' + self.__get_conditioning_fact(cond, step))
                                            if '>' in cond and '<>' not in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is over ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '>' + self.__get_conditioning_fact(cond, step))
                                            if '<' in cond and '<>' not in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is under ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '<' + self.__get_conditioning_fact(cond, step))
                                            if '!=' in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is not ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '!=' + self.__get_conditioning_fact(cond, step))
                                            if '<>' in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is not ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '<>' + self.__get_conditioning_fact(cond, step))
                                            if '=' in cond and '\"' not in cond and '>' not in cond and '<' not in cond:
                                                conditions_descr += ', and ' + self.__get_conditioned_fact(cond, step) + \
                                                                    ' is equal to ' + self.__get_conditioning_fact(cond, step)
                                                realized_atom.append(self.__get_conditioned_fact(cond, step) + '=' + self.__get_conditioning_fact(cond, step))
                                            if '=' in cond and '\"' in cond and '>' not in cond and '<' not in cond:
                                                conditions_descr += ', and there is ' + self.__get_conditioning_fact(cond, step).replace("\"",'')
                                                realized_atom.append(self.__get_conditioning_fact(cond, step).replace("\"",''))


                                    # verbalize the head
                                    head_name = step['name']
                                    head_descr = self.__get_fact_description(preds_descr, head_name,
                                                                             step['pattern'], nulls_in_step)

                                    # update the output file with the new verbalized step
                                    if head_descr:
                                        head_descr = ", then " + head_descr
                                        try:
                                            chase_step_descr = body_descr + conditions_descr + head_descr + algebric_descr
                                            del(cond)
                                        except:
                                            try:
                                                chase_step_descr = body_descr + conditions_descr + head_descr
                                                del(cond)
                                            except:
                                                chase_step_descr = body_descr + head_descr

                                        if 'vatom' not in head_name:
                                            conditions_descr = ''

                                        # delete double whitespaces
                                        chase_step_descr = chase_step_descr.replace('  ',' ')
                                        # remove the first character if it is a space
                                        if chase_step_descr[0] == " ":
                                            chase_step_descr = chase_step_descr[1:]
                                        # capitalize the first letter
                                        chase_step_descr = chase_step_descr[0].upper() + chase_step_descr[1:]

                                        if first_step:
                                            first_step = False
                                        else:
                                            out.write('\n,')
                                        vstep = {"sentence": chase_step_descr + ".",
                                                 "number": step['number'],
                                                 "derived_fact": step['name'],
                                                 "type": "intensional",
                                                 "body_atoms": ','.join(realized_atom)}
                                        json.dump(vstep, out, separators=(",", ":"))

                                    else:
                                        try:
                                            propagate_condition = cond ## ADD MULTIPLE CONDITIONS
                                        except: None


                                # if instead it is an extensional ground fact
                                else:
                                    fact_name = step['name']
                                    chase_step_descr = self.__get_fact_description(preds_descr, fact_name,
                                                                                   step['pattern'], nulls_in_step)
                                    realized_atom.append(fact_name)

                                    # delete double whitespaces
                                    chase_step_descr = chase_step_descr.replace('  ',' ')
                                    # remove the first character if it is a space
                                    if chase_step_descr[0] == " ":
                                        chase_step_descr = chase_step_descr[1:]
                                    # capitalize the first letter
                                    chase_step_descr = chase_step_descr[0].upper() + chase_step_descr[1:]

                                    if first_step:
                                        first_step = False
                                    else:
                                        out.write('\n,')

                                    vstep = {"sentence": chase_step_descr + ".",
                                             "number": step['number'],
                                             "derived_fact": step['name'],
                                             "type": "extensional",
                                             "body_atoms": ''}
                                    json.dump(vstep, out, separators=(",", ":"))

                        out.write('\n]')

        except Exception as e:
            print(f"An error occurred: {e}")
