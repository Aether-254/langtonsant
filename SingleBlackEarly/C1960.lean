import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1960 : checkSingleBlackFast (-71, -48) 20165 .east (33, 18) (10, -52) = true := by
  decide +kernel

end LangtonsAnt
