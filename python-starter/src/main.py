import sys
from parse import parse_policy, parse_typing
from verify import check_policy, verify, VerifyException
from pca_logic import (
    stringify_policy,
    stringify_typing
)

class ServeExitState:
    SUCCESS = 0
    ERROR = 1
    FAILURE = 2

class CmdLineArgs:
    def __init__(self, policy_file: str, proof_file: str):
        self.policy_file = policy_file
        self.proof_file = proof_file

def parse_cmd_line_args() -> CmdLineArgs:
    argv = sys.argv
    if len(argv) < 3:
        print("expected 2 arguments")
        sys.exit(ServeExitState.ERROR)
    return CmdLineArgs(policy_file=argv[1], proof_file=argv[2])

def run(cmd: CmdLineArgs):
    try:
        with open(cmd.policy_file, 'r') as f:
            policy = f.read()
        user_policy = parse_policy(policy)
        print(stringify_policy(user_policy))
        check_policy(user_policy)

        with open(cmd.proof_file, 'r') as f:
            proof = f.read()
        m, p = parse_typing(proof)
        print(f"|-\n{stringify_typing(m, p)}\n")
        
        verify(user_policy, m, p)

        print(f"success")
        sys.exit(ServeExitState.SUCCESS)

    except Exception as e:
        if isinstance(e, VerifyException):
            print(str(e))
            print("failure")
            sys.exit(ServeExitState.FAILURE)
        else:
            print(str(e))
            print("error")
            sys.exit(ServeExitState.ERROR)
        

def main():
    try:
        args = parse_cmd_line_args()
        run(args)
    except Exception as e:
        print(str(e))
        print("error")
        sys.exit(ServeExitState.ERROR)


if __name__ == "__main__":
    main()
