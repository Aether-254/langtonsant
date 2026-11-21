import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1800 : checkSingleBlackFast (-55, -30) 20647 .east (30, 9) (-16, -48) = true := by
  decide +kernel

end LangtonsAnt
