import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1762 : checkSingleBlackFast (-53, -30) 19229 .east (24, 9) (1, -43) = true := by
  decide +kernel

end LangtonsAnt
