import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2019 : checkSingleBlackFast (-77, -49) 25633 .east (34, 22) (12, -57) = true := by
  decide +kernel

end LangtonsAnt
