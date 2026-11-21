import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0688 : checkSingleBlackFast2 (18, -11) 12188 .south (-6, -3) (-22, -15) = true := by
  decide +kernel

end LangtonsAnt
