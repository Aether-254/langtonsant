import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1982 : checkSingleBlackFast (-73, -50) 20269 .east (34, 19) (11, -53) = true := by
  decide +kernel

end LangtonsAnt
