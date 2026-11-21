import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0698 : checkSingleBlackFast (20, -9) 8515 .west (-7, 8) (-21, -7) = true := by
  decide +kernel

end LangtonsAnt
