import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0544 : checkSingleBlackFast (7, -6) 4157 .west (-10, 1) (-15, -11) = true := by
  decide +kernel

end LangtonsAnt
