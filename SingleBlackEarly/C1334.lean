import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1334 : checkSingleBlack (-16, 16) 13283 .east (1, -9) (-28, -5) = true := by
  decide +kernel

end LangtonsAnt
