class MemberStats:
    def __init__(self, member, member_count, dead_count, new_count, suspect_timeout, disseminations, max_updates,
                    lose_every_nth, peer_group_size, initial_contacts):
        self.member = member
        self.member_count = member_count
        self.dead_count = dead_count
        self.new_count = new_count
        self.suspect_timeout = suspect_timeout
        self.disseminations = disseminations
        self.max_updates = max_updates
        self.lose_every_nth = lose_every_nth
        self.peer_group_size = peer_group_size
        self.initial_contacts = initial_contacts
        
        self.stats = dict()

    def add_metric(self, name, val):
        if name not in self.stats:
            self.stats[name] = list()

        self.stats[name].append(val)

    def get_metric(self, name   ):
        return self.stats[name]