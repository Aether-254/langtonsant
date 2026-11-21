import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0009 : checkSingleBlackFast (-2, 0) 1574 .south (-5, -4) (-10, -5) = true := by
  decide +kernel

end LangtonsAnt
