import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1157 : checkSingleBlackFast (26, -15) 12016 .north (-6, 3) (-30, 5) = true := by
  decide +kernel

end LangtonsAnt
