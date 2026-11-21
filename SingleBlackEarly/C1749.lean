import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1749 : checkSingleBlackFast (-47, -29) 11904 .north (13, 5) (-39, -21) = true := by
  decide +kernel

end LangtonsAnt
