import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0417 : checkSingleBlackFast (17, 0) 8886 .south (-5, -4) (-22, -15) = true := by
  decide +kernel

end LangtonsAnt
