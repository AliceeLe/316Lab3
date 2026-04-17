import pca_logic as pca

class VerifyException(Exception):
    """
    Exception raised during verification errors.

    Args:
        message (str): The error message describing the issue.
    """
    def __init__(self, message: str):
        super().__init__(message)
        self.message = message


def check_policy(gamma: pca.Policy):
    """
    Checks if the given policy `gamma` is well-formed.

    Args:
        gamma (Policy): The policy to check.

    Raises:
        VerifyException: If `gamma` is not a well-formed policy.
    """
    raise NotImplementedError("unimplemented")


def verify(gamma: pca.Policy, m: pca.Proof, p: pca.Form):
    """
    Verifies that the judgment `gamma ⊢ m ⇐ p` holds.

    Args:
        gamma (Policy): The policy under which to verify the proof.
        m (Proof): The proof to verify.
        p (Form): The formula to verify.

    Raises:
        VerifyException: If the verification `gamma ⊢ m ⇐ p` fails.
    """
    raise NotImplementedError("unimplemented")
