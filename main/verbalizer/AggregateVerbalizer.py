import json
import logging
import collections


'''
    This class performs the aggregation of verbalizations of the chase graph,
    according to the fact requested in input, and generates a .txt file with it
    
    __author__: teodorobaldazzi
    __author__: andreacolombo
'''

class VerbalizationFinder:

    logging.getLogger().setLevel(logging.INFO)

    '''
    Function to find parent verbalization
        :param number: number of step for which we are looking for the verbalization
        :param chase_verb: verbalized chase graph
        :param explanation: list to append new verbalization
    '''

    def __find_verb(self, number, chase_verb, explanation, derived_facts):
            for i in range(len(chase_verb)):
                for j in range(len(chase_verb[i]['number'])):
                    if chase_verb[i]['number'][j] == number:
                        explanation.append(chase_verb[i]['sentence'])
                        derived_facts.append(chase_verb[i]['derived_fact'])


    def __find_parent(self, number, chase_verb, explanation, driver_numbers, already_visited, atom):
        for i in range(len(chase_verb)):
            if len(chase_verb[i]['number']) > 0:
                origin_numbers = list()
                components = list()
                for j in range(len(chase_verb[i]['number'])):
                    origin_numbers.append(chase_verb[i]['number'][j].split('.')[0])
                    components.append(chase_verb[i]['number'])
                origin_numbers = [x for x in origin_numbers if x != '']

            for j in range(len(chase_verb[i]['number'])):
                if len(already_visited) > 0:
                    if chase_verb[i]['number'][j] == number and all(item in driver_numbers for item in origin_numbers) and all(item not in components[0] for item in already_visited):
                        # print(components[0])
                        # print(already_visited)
                        explanation.append(chase_verb[i]['rule'])
                        atom.append(chase_verb[i]['name'])
                else:
                    if chase_verb[i]['number'][j] == number and all(item in driver_numbers for item in origin_numbers):
                        explanation.append(chase_verb[i]['rule'])
                        atom.append(chase_verb[i]['name'])

    '''
        This method creates a .txt file with the verbalized explanation for the input fact

        :param chase_path: path to verbalized chase graph file
        :param fact_to_explain: a fact in the chase to be explained
        :param explain_derivation: boolean to have explanation of the derivation or of individual edge
        :param output_path: path to output file
    '''

    def verbalize_fact(self, chase_path, output_path, fact_to_explain, explain_derivation):
        # Open chase graph verbalized
        with open(chase_path) as c:
            verbalized = json.load(c)

        # Text file to write explanation
        with open(output_path + "verb_fact.json", "w") as out:
            out.write('[')
            first_step = True
            # Delete vatom steps to allow retrival of real steps
            # for i in range(len(verbalized)):
            #     for j in range(len(verbalized[i]['number'])):
            #         verbalized[i]['number'][j] = verbalized[i]['number'][j].replace('T','')

            # List to store verbalizations
            verbs = list()
            atoms = list()
            bodies = list()

            # Loop through the verbalization to get the verbalization
            # of the required fact, plus the corresponding number, by which
            # we can then retrieve the previous steps
            for j in range(len(verbalized)):
                if verbalized[j]['derived_fact'] == fact_to_explain:
                    K = verbalized[j]['number']
                    verbs.append(verbalized[j]['sentence'])
                    atoms.append(verbalized[j]['derived_fact'])
                    break
           
            # Retrieve all previous verbalization steps
            for k in range(len(K)): 
                nested_verb = K[k].split('.')
                for j in range(len(nested_verb)):
                    parent_verb = ".".join([str(item) for item in K[k].split('.')[:-1]])
                    self.__find_verb(parent_verb, verbalized, verbs, atoms)
                    K[k] = parent_verb
            
            # Write in a file depending on the request
            verbs = list(dict.fromkeys(verbs))
            verbs.reverse()
            atoms = list(dict.fromkeys(atoms))
            atoms.reverse()
            # Retrieve body atoms
            for i in atoms:
                for j in range(len(verbalized)):
                    if verbalized[j]['derived_fact'] == i:
                        bodies.append(verbalized[j]['body_atoms'])

            if explain_derivation:
                for step in range(len(verbs)):
                        if first_step:
                            first_step = False
                        else:
                            out.write('\n,')
                        vstep = {"Verb_rule": verbs[step],
                                 "atom": atoms[step],
                                 "body": bodies[step]}
                        json.dump(vstep, out, separators=(",", ":"))
                out.write(']')
            else:
                out.write(verbs[0])


    def get_chase_fact(self, file1_path, fact_to_explain):
        with open(file1_path) as c:
            num_chase_graph = json.load(c)
        # print('\n')
        # print(fact_to_explain)
        rules = list()
        atom = list()
        new_chase = list()
        for i in range(len(num_chase_graph)):
            if num_chase_graph[i]['name'] == fact_to_explain:
                rules.append(num_chase_graph[i]['rule'])
                atom.append(num_chase_graph[i]['name'])
                number = num_chase_graph[i]['number']
                break
            else:
                new_chase.append(num_chase_graph[i])

        num_chase_graph = new_chase.copy()

        driver_numbers = list()
        for i in range(len(number)):
            driver_numbers.append(number[i].split('.')[0])
        # print(rules)
        # print(driver_numbers)

        visit = list()
        number.reverse()

            # Retrieve all previous verbalization steps
        for i in range(len(number)):
            nested_verb = number[i].split('.')
            for j in range(len(nested_verb)):
                parent_verb = ".".join([str(item) for item in number[i].split('.')[:-1]])
                # print(visit)
                # print(parent_verb)
                self.__find_parent(parent_verb, num_chase_graph, rules, driver_numbers, visit, atom)
                visit.append(parent_verb)
                # print(atom[-1])
                number[i] = parent_verb

        # rules = list(dict.fromkeys(rules))

        atom = [atom[ele] for ele in range(len(rules)) if rules[ele] != None]
        rules = [ele for ele in rules if ele != None]
        rules = [ele.replace('not ','not_').replace(' ','').replace('not_','not ') for ele in rules]
        # rules.sort(reverse=True)

        return(rules, atom)

