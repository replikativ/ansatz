import Domain
namespace App
def calculate (n : Nat) : Nat := (Domain.credit { balance := n, enabled := true } 7).balance + Domain.bonus
def account (n : Nat) : Domain.Account := Domain.credit { balance := n, enabled := true } 7
end App
