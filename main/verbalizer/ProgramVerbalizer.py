import json
import logging
from main.verbalizer.utilsFunctions import split_condition_from_rule

'''
    This class performs the verbalization of the Vadalog program.
    
    It receives as input a program.json file with the program, in the form:
    [{"rule":vadalog rule}
    ]
    and a predicates.json file with the verbalized descriptions of the predicates, in the form:
    [{"predicate":predicate with generic args,"description":generic verbalization of the predicate}
    ]
    
    It returns a verb_program.txt file with the verbalization of the program
    
    __author__: teodorobaldazzi
    __author__: andreacolombo
'''
class ProgramVerbalizer:

    logging.getLogger().setLevel(logging.INFO)


    '''
        :param preds_descr: the deserialized pred_file
        :param atom: an atom in a rule of that predicate
    '''
    def __get_pred_description(self, preds_descr, atom):
        # extract name and args of the current atom
        atom_name = atom.partition('(')[0]
        atom_args = atom.split('(')[1].split(')')[0].split(',')

        # for each predicate in the file (until the right description is found)
        for pred_descr in preds_descr:
            # extract name and args of the predicate
            pred = pred_descr['predicate']
            pred_name = pred.partition('(')[0]
            pred_parts = pred.split('(')[1].split(')')[0].split(',')
            # if the fact belongs to the current predicate
            if pred_name == atom_name and len(pred_parts) == len(atom_args):
                # extract the description of the predicate
                atom_descr = pred_descr['description']
                # verbalize the fact according to the description of the predicate
                # by substituting the generic args of the predicate with the ones of the atom
                for i in range(len(pred_parts)):
                    fact_arg = atom_args[i]
                    atom_descr = atom_descr.replace(pred_parts[i], ' ' + fact_arg)
                # the atom has been verbalized, so return it
                return atom_descr  
            
        return None


    '''
        This method creates a .json file with the verbalized program
        
        :param program_path: path to the program.json file with the program
        :param predicates_path: path to the predicates.json file with the predicates' description
        :param output_path: path to output file
    '''
    def verbalize_program(self, program_path, predicates_path, output_path, is_recursive = False):
        try:
            with open(program_path) as v:
                # deserialize progr file
                program = json.load(v)
                with open(predicates_path) as p:
                    # deserialize pred file
                    preds_descr = json.load(p)
                    # create new output file or rewrite existing one
                    with open(output_path + "verb_program.txt", "w") as out:
                        # for each rule in the program, we split the body between predicates and
                        # eventual conditions on variables -> useful for verbalizing conditions
                        for rule in program:
                            # print(rule)
                            rule['rule'], rule['conditions'], rule['algebric'] = split_condition_from_rule(rule)
                            head, body = rule['rule'].split(":-")[0], rule['rule'].split(":-")[1]
                            body = '-'+body
                            # Detect recursion
                            if ','+head.split("(")[0] in body or '-'+head.split("(")[0] in body:
                                type_recursion = body.split('),')
                                # left recursion
                                if head.split("(")[0] in type_recursion[0]:
                                    left = ' indirectly via ENTITY'
                                    right = ''
                                # right recursion
                                if head.split("(")[0] in type_recursion[1]:
                                    left = ''
                                    right = ' indirectly via ENTITY'
                            body = body[1:]
                            # verbalize the body
                            body = body.split('),')
                            
                            if body[0]:
                                body_descr = ""
                                # this is the case of linear rules
                                if len(body) == 1:
                                    body_descr = "Since " + self.__get_pred_description(preds_descr, body[0])
                                # this is the case of join rules
                                if len(body) > 1:
                                    for atom in body:
                                        # if it is not a negated atom
                                        if not atom.startswith("not "):

                                            if not is_recursive:
                                                # distinct verbalization if it is the first fact in the join
                                                if body_descr == "":
                                                    body_descr = "Since " + self.__get_pred_description(preds_descr, atom)
                                                else:
                                                    body_descr += ", and " + self.__get_pred_description(preds_descr, atom)
                                            else:
                                                if body_descr == "":
                                                    body_descr = "Since " + self.__get_pred_description(preds_descr, atom) + right
                                                else:
                                                    body_descr += ", and " + self.__get_pred_description(preds_descr, atom) + left

                                        # if it is a negated atom
                                        else:
                                            atom_without_neg = atom[4:]
                                            # distinct verbalization if it is the first fact in the join
                                            if body_descr == "":
                                                body_descr += 'Since it is not true that ' + \
                                                              self.__get_pred_description(preds_descr, atom_without_neg)
                                            else:
                                                body_descr += ', and it is not true that ' + \
                                                              self.__get_pred_description(preds_descr, atom_without_neg)
                                                                
                                conditions_descr = ''
                                # add verbalizations of (eventual) conditions
                                if len(rule['conditions']) > 0 :
                                    conditions = rule['conditions']
                                    for cond in conditions:
                                     if cond.split('<')[0] in head.split('(')[1]:
                                        # different verbalization according to condition
                                        if '>=' in cond:
                                            conditions_descr += ', and ' + cond.split('>=')[0].strip() + \
                                                                ' is equal to or over ' + cond.split('>=')[1].strip()
                                        if '<=' in cond:
                                            conditions_descr += ', and ' + cond.split('<=')[0].strip() + \
                                                                ' is equal to or under ' + cond.split('<=')[1].strip()
                                        if '>' in cond and '<>' not in cond:
                                            conditions_descr += ', and ' + cond.split('>')[0].strip() + \
                                                                ' is over ' + cond.split('>')[1].strip()
                                        if '<' in cond and '<>' not in cond:
                                            conditions_descr += ', and ' + cond.split('<')[0].strip() + \
                                                                ' is under ' + cond.split('<')[1].strip()
                                        if '!=' in cond:
                                            conditions_descr += ', and ' + cond.split('!=')[0].strip() + \
                                                                ' is not ' + cond.split('!=')[1].strip()
                                        if '<>' in cond:
                                            conditions_descr += ', and ' + cond.split('<>')[0].strip() + \
                                                                ' is not ' + cond.split('<>')[1].strip()
                                        if '=' in cond and '\"' not in cond and '>' not in cond and '<' not in cond:
                                            conditions_descr += ', and ' + cond.split('=')[0].strip() + \
                                                                ' is equal to ' + cond.split('=')[1].strip()
                                        if '=' in cond and '\"' in cond and '>' not in cond and '<' not in cond:
                                            conditions_descr += ', and there is ' + cond.split('=')[1].strip()

                                # verbalize the head
                                head_descr = self.__get_pred_description(preds_descr, head)
                                 
                                algebric_descr = ""
                                # verbalize algebric operation
                                if len(rule['algebric']) > 0:
                                    for oper in rule['algebric']:
                                      if oper.split('=')[0] in head.split('(')[1]:
                                        if '=' in oper and 'msum' not in oper:
                                            algebric_descr += ', with ' + oper.split('=')[0] + ' given by ' + oper.split('=')[1]
                                        # elif '=' in oper and 'msum' in oper:
                                        #     algebric_descr += ', with ' + oper.split('=')[0] + ' given by the sum over all the contributors' # + oper.split('msum(')[1].split(',')[1].split(')')[0].replace('<','').replace('>','')

                                # update the output file with the new verbalized step
                                if head_descr:
                                    head_descr = ", then " + head_descr
                                    try:
                                        rule_step_descr = body_descr + conditions_descr + head_descr + algebric_descr  + "." + '\n'
                                    except:
                                        try:
                                            rule_step_descr = body_descr + conditions_descr + head_descr  + "." + '\n'
                                        except:
                                            rule_step_descr = body_descr + head_descr + "." '\n'
                                    # delete double whitespaces
                                    rule_step_descr = rule_step_descr.replace('  ',' ')
                                    out.write(rule_step_descr)
        except Exception as e:
            print(f"An error occurred: {e}")