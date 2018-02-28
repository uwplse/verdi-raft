import urllib3

class Client(object):
    class NoLeader(Exception):
        pass

    @classmethod
    def find_leader(cls, cluster):
        # cluster should be a list of [(host, port)] pairs
        for (host, port) in cluster:
            c = cls(host, port)
            r = c.http.request('GET', c.base_url + '/v2/stats/self')
            if '"state":"StateLeader"' in r.data:
                return (host, port)
        raise cls.NoLeader
    

    def __init__(self, host, port):
        self.base_url = 'http://' + host + ':' + str(port)
        self.http = urllib3.PoolManager()

    def get(self, key):
        r = self.http.request('GET', self.base_url + '/v2/keys/' + str(key) + '?quorum=true')
        return r.data

    def put(self, key, value):
        r = self.http.request('PUT', self.base_url + '/v2/keys/' + str(key),
                              fields={'value': str(value)})
        return r.data
