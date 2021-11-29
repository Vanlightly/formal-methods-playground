class ExecutionStats:
    def __init__(self, exec_no, member_count, dead_count, new_count, suspect_timeout, disseminations, max_updates,
                    lose_every_nth, peer_group_size, initial_contacts):
        self.exec_no = exec_no
        self.member_count = member_count
        self.dead_count = dead_count
        self.new_count = new_count
        self.suspect_timeout = suspect_timeout
        self.disseminations = disseminations
        self.max_updates = max_updates
        self.lose_every_nth = lose_every_nth
        self.peer_group_size = peer_group_size
        self.initial_contacts = initial_contacts
        
        self.rounds = dict()
        self.total_rounds = 0

    def add_metric(self, round_no, name, val):
        if round_no not in self.rounds:
            self.rounds[round_no] = dict()

        if round_no > self.total_rounds:
            self.total_rounds = round_no

        self.rounds[round_no][name] = val

    def get_metric(self, round_no, name):
        if name not in self.rounds[round_no]:
            print(f"{name} not in round {round_no} for exec_no {self.exec_no}")
            return 0
            
        return self.rounds[round_no][name]

    def has_round(self, round_no):
        return round_no in self.rounds