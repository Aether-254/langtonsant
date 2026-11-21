import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0390 : checkSingleBlackFast (12, -4) 9635 .west (-10, 2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
